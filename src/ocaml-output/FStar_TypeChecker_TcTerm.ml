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
      FStar_TypeChecker_Env.mpreprocess =
        (uu___8_5.FStar_TypeChecker_Env.mpreprocess);
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
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_13.FStar_TypeChecker_Env.mpreprocess);
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
                   FStar_TypeChecker_Util.check_and_ascribe env e lc t'  in
                 (match uu____506 with
                  | (e1,lc1,g) ->
                      ((let uu____523 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium
                           in
                        if uu____523
                        then
                          let uu____526 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1  in
                          let uu____528 =
                            FStar_Syntax_Print.term_to_string t'  in
                          let uu____530 =
                            FStar_TypeChecker_Rel.guard_to_string env g  in
                          let uu____532 =
                            FStar_TypeChecker_Rel.guard_to_string env guard
                             in
                          FStar_Util.print4
                            "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                            uu____526 uu____528 uu____530 uu____532
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ  in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard  in
                        let uu____539 =
                          let uu____544 =
                            ((FStar_All.pipe_right tlc FStar_Util.is_left) &&
                               (FStar_TypeChecker_Util.should_return env
                                  (FStar_Pervasives_Native.Some e1) lc1))
                              && (FStar_TypeChecker_Common.is_pure_lcomp lc1)
                             in
                          if uu____544
                          then
                            let uu____556 =
                              FStar_TypeChecker_Util.lcomp_univ_opt lc1  in
                            match uu____556 with
                            | (u_opt,g_lc) ->
                                let uu____573 =
                                  let uu____574 =
                                    FStar_TypeChecker_Util.return_value env
                                      u_opt t1 e1
                                     in
                                  FStar_All.pipe_right uu____574
                                    FStar_TypeChecker_Common.lcomp_of_comp
                                   in
                                let uu____575 =
                                  FStar_TypeChecker_Env.conj_guard g1 g_lc
                                   in
                                (uu____573, uu____575)
                          else (lc1, g1)  in
                        match uu____539 with
                        | (lc2,g2) ->
                            let msg =
                              let uu____593 =
                                FStar_TypeChecker_Env.is_trivial_guard_formula
                                  g2
                                 in
                              if uu____593
                              then FStar_Pervasives_Native.None
                              else
                                FStar_All.pipe_left
                                  (fun _622  ->
                                     FStar_Pervasives_Native.Some _622)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     t1 t')
                               in
                            let uu____623 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e1 lc2 g2
                               in
                            (match uu____623 with
                             | (lc3,g3) ->
                                 let uu____636 = set_lcomp_result lc3 t'  in
                                 ((memo_tk e1 t'), uu____636, g3)))))
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
        let uu____674 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____674 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____684 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t
               in
            (match uu____684 with
             | (e1,lc1,g_c) ->
                 let uu____700 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t  in
                 (match uu____700 with
                  | (e2,lc2,g) ->
                      let uu____716 = FStar_TypeChecker_Env.conj_guard g g_c
                         in
                      (e2, lc2, uu____716)))
  
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
        let uu____757 = ec  in
        match uu____757 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____780 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____780
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____785 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____785
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____791 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____815 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None  ->
                  let uu____820 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____823 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____823))
                     in
                  if uu____820
                  then
                    let uu____836 =
                      let uu____839 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____839  in
                    (uu____836, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____846 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____846
                     then
                       let uu____859 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____859,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____866 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____866
                        then
                          let uu____879 =
                            let uu____882 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____882  in
                          (uu____879, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____889 =
                             let uu____891 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env)
                                in
                             FStar_All.pipe_right uu____891
                               (FStar_TypeChecker_Env.is_layered_effect env)
                              in
                           if uu____889
                           then
                             let uu____904 =
                               let uu____910 =
                                 let uu____912 =
                                   let uu____914 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name
                                      in
                                   FStar_All.pipe_right uu____914
                                     FStar_Ident.string_of_lid
                                    in
                                 let uu____918 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____912 uu____918
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____910)  in
                             FStar_Errors.raise_error uu____904
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____934 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  ()
                                 in
                              if uu____934
                              then
                                let uu____947 =
                                  let uu____950 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c
                                     in
                                  match uu____950 with
                                  | (uu____959,uu____960,g) ->
                                      FStar_Pervasives_Native.Some g
                                   in
                                (FStar_Pervasives_Native.None, c, uu____947)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None)))))
               in
            (match uu____791 with
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
                        | FStar_Pervasives_Native.Some uu____999 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____1002 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2  in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____1002
                           in
                        let uu____1003 =
                          FStar_TypeChecker_Common.lcomp_comp c3  in
                        match uu____1003 with
                        | (c4,g_c) ->
                            ((let uu____1017 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium
                                 in
                              if uu____1017
                              then
                                let uu____1021 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____1023 =
                                  FStar_Syntax_Print.comp_to_string c4  in
                                let uu____1025 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c
                                   in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1021 uu____1023 uu____1025
                              else ());
                             (let uu____1030 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c
                                 in
                              match uu____1030 with
                              | (e1,uu____1044,g) ->
                                  let g1 =
                                    let uu____1047 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1047
                                      "could not prove post-condition" g
                                     in
                                  ((let uu____1050 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium
                                       in
                                    if uu____1050
                                    then
                                      let uu____1053 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____1055 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1
                                         in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1053 uu____1055
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
                                    let uu____1061 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1
                                       in
                                    (e2, expected_c, uu____1061)))))))))
  
let no_logical_guard :
  'Auu____1071 'Auu____1072 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1071 * 'Auu____1072 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____1071 * 'Auu____1072 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____1094  ->
      match uu____1094 with
      | (te,kt,f) ->
          let uu____1104 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____1104 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1112 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____1118 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____1112 uu____1118)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1131 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1131 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1136 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1136
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1166 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1166 with
        | (head1,args) ->
            let uu____1211 =
              let uu____1226 =
                let uu____1227 = FStar_Syntax_Util.un_uinst head1  in
                uu____1227.FStar_Syntax_Syntax.n  in
              (uu____1226, args)  in
            (match uu____1211 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1243) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1270,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1271))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1348,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1349))::(pat,FStar_Pervasives_Native.None
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
             | uu____1433 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
  
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats 
let check_pat_fvs :
  'Auu____1477 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1477) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1513 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1520 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1513 uu____1520  in
          let uu____1521 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1548  ->
                    match uu____1548 with
                    | (b,uu____1555) ->
                        let uu____1556 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1556))
             in
          match uu____1521 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1563) ->
              let uu____1568 =
                let uu____1574 =
                  let uu____1576 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1576
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1574)  in
              FStar_Errors.log_issue rng uu____1568
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1602 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1602 with
        | (head1,args) ->
            let uu____1647 =
              let uu____1662 =
                let uu____1663 = FStar_Syntax_Util.un_uinst head1  in
                uu____1663.FStar_Syntax_Syntax.n  in
              (uu____1662, args)  in
            (match uu____1647 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1679) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1701::(hd1,uu____1703)::(tl1,uu____1705)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1772 = pat_terms hd1  in
                 let uu____1775 = pat_terms tl1  in
                 FStar_List.append uu____1772 uu____1775
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1779::(pat,uu____1781)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1866 -> [])
         in
      let rec aux t1 =
        let uu____1891 =
          let uu____1892 = FStar_Syntax_Subst.compress t1  in
          uu____1892.FStar_Syntax_Syntax.n  in
        match uu____1891 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1897 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1898 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1899 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1900 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1913 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1914 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1915 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1934 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1949 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1956 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1979 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1993 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____2016 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____2024 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____2024 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2057 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2074  ->
                   match uu____2074 with
                   | (t3,uu____2086) ->
                       let uu____2091 = aux t3  in
                       FStar_List.append acc uu____2091) uu____2057 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2095,uu____2096) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2138) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2144) -> aux t2  in
      let tlist =
        let uu____2152 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2152 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2175 =
                    let uu____2177 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2177  in
                  Prims.op_Hat s uu____2175) "" tlist
            in
         let uu____2181 =
           let uu____2187 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2187)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2181)
  
let check_smt_pat :
  'Auu____2202 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2202) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2243 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2243
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2246;
                  FStar_Syntax_Syntax.effect_name = uu____2247;
                  FStar_Syntax_Syntax.result_typ = uu____2248;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2252)::[];
                  FStar_Syntax_Syntax.flags = uu____2253;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2315 -> failwith "Impossible"
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
              let uu___373_2378 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___373_2378.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___373_2378.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___373_2378.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___373_2378.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___373_2378.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___373_2378.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___373_2378.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___373_2378.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___373_2378.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___373_2378.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___373_2378.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___373_2378.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___373_2378.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___373_2378.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___373_2378.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___373_2378.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___373_2378.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___373_2378.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___373_2378.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___373_2378.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___373_2378.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___373_2378.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___373_2378.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___373_2378.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___373_2378.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___373_2378.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___373_2378.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___373_2378.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___373_2378.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___373_2378.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___373_2378.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___373_2378.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___373_2378.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___373_2378.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___373_2378.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___373_2378.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___373_2378.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___373_2378.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___373_2378.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___373_2378.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___373_2378.FStar_TypeChecker_Env.erasable_types_tab)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2404 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2404
               then
                 let uu____2407 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2410 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2407 uu____2410
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2444  ->
                         match uu____2444 with
                         | (b,uu____2454) ->
                             let t =
                               let uu____2460 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2460
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2463 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2464 -> []
                              | uu____2479 ->
                                  let uu____2480 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2480])))
                  in
               let as_lex_list dec =
                 let uu____2493 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2493 with
                 | (head1,uu____2513) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2541 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2549 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2558  ->
                         match uu___1_2558 with
                         | FStar_Syntax_Syntax.DECREASES uu____2560 -> true
                         | uu____2564 -> false))
                  in
               match uu____2549 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2571 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2592 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2621 =
              match uu____2621 with
              | (l,t,u_names) ->
                  let uu____2645 =
                    let uu____2646 = FStar_Syntax_Subst.compress t  in
                    uu____2646.FStar_Syntax_Syntax.n  in
                  (match uu____2645 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2705  ->
                                 match uu____2705 with
                                 | (x,imp) ->
                                     let uu____2724 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2724
                                     then
                                       let uu____2733 =
                                         let uu____2734 =
                                           let uu____2737 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2737
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2734
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2733, imp)
                                     else (x, imp)))
                          in
                       let uu____2744 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2744 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2765 =
                                let uu____2770 =
                                  let uu____2771 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2780 =
                                    let uu____2791 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2791]  in
                                  uu____2771 :: uu____2780  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2770
                                 in
                              uu____2765 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2826 = FStar_Util.prefix formals2  in
                            (match uu____2826 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___440_2889 = last1  in
                                   let uu____2890 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___440_2889.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___440_2889.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2890
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2926 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Medium
                                      in
                                   if uu____2926
                                   then
                                     let uu____2929 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2931 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2933 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2929 uu____2931 uu____2933
                                   else ());
                                  (l, t', u_names))))
                   | uu____2940 ->
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
               let uu____3004 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____3004)
  
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____3027 =
      let uu____3028 = FStar_Syntax_Subst.compress e  in
      uu____3028.FStar_Syntax_Syntax.n  in
    match uu____3027 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1,(FStar_Util.Inr uu____3040,uu____3041),uu____3042) ->
        let uu____3089 =
          let uu____3090 = FStar_Syntax_Subst.compress e1  in
          uu____3090.FStar_Syntax_Syntax.n  in
        (match uu____3089 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____3137 =
               let uu____3138 = FStar_Syntax_Subst.compress head1  in
               uu____3138.FStar_Syntax_Syntax.n  in
             (match uu____3137 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____3150 =
                    let uu____3157 = FStar_All.pipe_right args FStar_List.hd
                       in
                    FStar_All.pipe_right uu____3157
                      (fun uu____3213  ->
                         match uu____3213 with | (e2,aqual) -> (l, e2, aqual))
                     in
                  FStar_All.pipe_right uu____3150
                    (fun _3266  -> FStar_Pervasives_Native.Some _3266)
              | uu____3267 -> FStar_Pervasives_Native.None)
         | uu____3274 -> FStar_Pervasives_Native.None)
    | uu____3281 -> FStar_Pervasives_Native.None
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3918 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3918
       then
         let uu____3921 =
           let uu____3923 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3923  in
         let uu____3925 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____3927 = FStar_Syntax_Print.term_to_string e  in
         let uu____3929 =
           let uu____3931 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3931  in
         let uu____3932 =
           let uu____3934 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____3934 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3921 uu____3925 uu____3927 uu____3929 uu____3932
       else ());
      (let uu____3943 =
         FStar_Util.record_time
           (fun uu____3962  ->
              tc_maybe_toplevel_term
                (let uu___484_3965 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___484_3965.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___484_3965.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___484_3965.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___484_3965.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___484_3965.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___484_3965.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___484_3965.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___484_3965.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___484_3965.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___484_3965.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___484_3965.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___484_3965.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___484_3965.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___484_3965.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___484_3965.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___484_3965.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___484_3965.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___484_3965.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___484_3965.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___484_3965.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___484_3965.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___484_3965.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___484_3965.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___484_3965.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___484_3965.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___484_3965.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___484_3965.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___484_3965.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___484_3965.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___484_3965.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___484_3965.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___484_3965.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___484_3965.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___484_3965.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___484_3965.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___484_3965.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___484_3965.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___484_3965.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___484_3965.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___484_3965.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___484_3965.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____3943 with
       | (r,ms) ->
           ((let uu____3990 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3990
             then
               ((let uu____3994 =
                   let uu____3996 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3996
                    in
                 let uu____3998 = FStar_Syntax_Print.term_to_string e  in
                 let uu____4000 =
                   let uu____4002 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____4002  in
                 let uu____4003 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3994 uu____3998 uu____4000 uu____4003);
                (let uu____4006 = r  in
                 match uu____4006 with
                 | (e1,lc,uu____4015) ->
                     let uu____4016 =
                       let uu____4018 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4018
                        in
                     let uu____4020 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4022 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4024 =
                       let uu____4026 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4026  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4016 uu____4020 uu____4022 uu____4024))
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
      (let uu____4044 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4044
       then
         let uu____4047 =
           let uu____4049 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4049  in
         let uu____4051 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4053 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4047 uu____4051
           uu____4053
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4064 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4094 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4101 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4114 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4115 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4116 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4117 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4118 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4137 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4152 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4159 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4175 =
             match uu___2_4175 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4181 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____4197 =
                 let uu____4198 = FStar_Syntax_Subst.compress t  in
                 uu____4198.FStar_Syntax_Syntax.n  in
               match uu____4197 with
               | FStar_Syntax_Syntax.Tm_name uu____4202 -> true
               | uu____4204 -> false  in
             FStar_Util.for_some
               (fun uu____4214  ->
                  match uu____4214 with
                  | (uu____4220,t) ->
                      let uu____4222 = is_name1 t  in
                      Prims.op_Negation uu____4222)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4241  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4284  ->
                       match uu____4284 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___557_4313 = qi  in
                  let uu____4314 =
                    FStar_List.map
                      (fun uu____4342  ->
                         match uu____4342 with
                         | ((bv,uu____4358),bv') ->
                             let uu____4370 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4370)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___557_4313.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4314
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
                         let uu____4382 =
                           let uu____4389 =
                             let uu____4390 =
                               let uu____4404 =
                                 let uu____4407 =
                                   let uu____4408 =
                                     let uu____4415 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4415
                                      in
                                   [uu____4408]  in
                                 FStar_Syntax_Subst.close uu____4407 t  in
                               ((false, [lb]), uu____4404)  in
                             FStar_Syntax_Syntax.Tm_let uu____4390  in
                           FStar_Syntax_Syntax.mk uu____4389  in
                         uu____4382 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4451 =
                  FStar_List.fold_right
                    (fun uu____4487  ->
                       fun uu____4488  ->
                         match (uu____4487, uu____4488) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4557 = tc_term env_tm tm  in
                             (match uu____4557 with
                              | (tm1,uu____4575,g) ->
                                  let uu____4577 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4577))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4451 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___585_4619 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___585_4619.FStar_Syntax_Syntax.qkind);
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
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term
                   in
                let uu____4630 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4630 with
                 | (env',uu____4644) ->
                     let uu____4649 =
                       tc_term
                         (let uu___594_4658 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___594_4658.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___594_4658.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___594_4658.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___594_4658.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___594_4658.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___594_4658.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___594_4658.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___594_4658.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___594_4658.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___594_4658.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___594_4658.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___594_4658.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___594_4658.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___594_4658.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___594_4658.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___594_4658.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___594_4658.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___594_4658.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___594_4658.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___594_4658.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___594_4658.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___594_4658.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___594_4658.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___594_4658.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___594_4658.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___594_4658.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___594_4658.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___594_4658.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___594_4658.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___594_4658.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___594_4658.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___594_4658.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___594_4658.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___594_4658.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___594_4658.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___594_4658.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___594_4658.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___594_4658.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___594_4658.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___594_4658.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___594_4658.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4649 with
                      | (qt1,uu____4667,uu____4668) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4674 =
                            let uu____4681 =
                              let uu____4686 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4686  in
                            value_check_expected_typ env1 top uu____4681
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4674 with
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
           { FStar_Syntax_Syntax.blob = uu____4703;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4704;
             FStar_Syntax_Syntax.ltyp = uu____4705;
             FStar_Syntax_Syntax.rng = uu____4706;_}
           ->
           let uu____4717 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4717
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4724 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4724 with
            | (e2,c,g) ->
                let g1 =
                  let uu___624_4741 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___624_4741.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___624_4741.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___624_4741.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4742 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4742, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4784 = FStar_Syntax_Util.type_u ()  in
           (match uu____4784 with
            | (t,u) ->
                let uu____4797 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4797 with
                 | (e2,c,g) ->
                     let uu____4813 =
                       let uu____4830 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4830 with
                       | (env2,uu____4854) -> tc_smt_pats env2 pats  in
                     (match uu____4813 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___647_4892 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___647_4892.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___647_4892.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___647_4892.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4893 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4912 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4893, c, uu____4912))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4918 =
             let uu____4919 = FStar_Syntax_Subst.compress e1  in
             uu____4919.FStar_Syntax_Syntax.n  in
           (match uu____4918 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4928,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4930;
                               FStar_Syntax_Syntax.lbtyp = uu____4931;
                               FStar_Syntax_Syntax.lbeff = uu____4932;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4934;
                               FStar_Syntax_Syntax.lbpos = uu____4935;_}::[]),e2)
                ->
                let uu____4966 =
                  let uu____4973 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4973 e11  in
                (match uu____4966 with
                 | (e12,c1,g1) ->
                     let uu____4983 = tc_term env1 e2  in
                     (match uu____4983 with
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
                            let uu____5007 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____5007
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5017 =
                              let uu____5024 =
                                let uu____5025 =
                                  let uu____5039 =
                                    let uu____5047 =
                                      let uu____5050 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____5050]  in
                                    (false, uu____5047)  in
                                  (uu____5039, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____5025  in
                              FStar_Syntax_Syntax.mk uu____5024  in
                            uu____5017 FStar_Pervasives_Native.None
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
                          let uu____5074 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5074)))
            | uu____5075 ->
                let uu____5076 = tc_term env1 e1  in
                (match uu____5076 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5098) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5110) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5129 = tc_term env1 e1  in
           (match uu____5129 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5150,(FStar_Util.Inr expected_c,_tacopt),uu____5153) when
           let uu____5200 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5200 FStar_Util.is_some ->
           let uu____5232 =
             let uu____5243 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5243 FStar_Util.must  in
           (match uu____5232 with
            | (effect_lid,e1,aqual) ->
                let uu____5317 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5317 with
                 | (env0,uu____5331) ->
                     let uu____5336 = tc_comp env0 expected_c  in
                     (match uu____5336 with
                      | (expected_c1,uu____5350,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5354 =
                              let uu____5356 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5356  in
                            if uu____5354
                            then
                              let uu____5359 =
                                let uu____5365 =
                                  let uu____5367 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5369 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5367 uu____5369
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5365)
                                 in
                              FStar_Errors.raise_error uu____5359
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5376 =
                              let uu____5378 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5378  in
                            if uu____5376
                            then
                              let uu____5381 =
                                let uu____5387 =
                                  let uu____5389 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5389
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5387)
                                 in
                              FStar_Errors.raise_error uu____5381
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5399 =
                                let uu____5402 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5402 u_c
                                 in
                              FStar_All.pipe_right uu____5399 FStar_Util.must
                               in
                            let e2 =
                              let uu____5408 =
                                let uu____5415 =
                                  let uu____5416 =
                                    let uu____5443 =
                                      let uu____5460 =
                                        let uu____5469 =
                                          FStar_Syntax_Syntax.mk_Total' repr
                                            (FStar_Pervasives_Native.Some u_c)
                                           in
                                        FStar_Util.Inr uu____5469  in
                                      (uu____5460,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (e1, uu____5443,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____5416
                                   in
                                FStar_Syntax_Syntax.mk uu____5415  in
                              uu____5408 FStar_Pervasives_Native.None
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5511 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5511
                             then
                               let uu____5515 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5515
                             else ());
                            (let uu____5520 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5520 with
                             | (e3,uu____5534,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5538 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5538
                                   then
                                     let uu____5542 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5544 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5542 uu____5544
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos  in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)]))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let uu____5591 =
                                       let uu____5598 =
                                         let uu____5599 =
                                           let uu____5626 =
                                             let uu____5629 =
                                               FStar_All.pipe_right
                                                 expected_c1
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5629
                                               (fun _5634  ->
                                                  FStar_Pervasives_Native.Some
                                                    _5634)
                                              in
                                           (tm1,
                                             ((FStar_Util.Inr expected_c1),
                                               _tacopt), uu____5626)
                                            in
                                         FStar_Syntax_Syntax.Tm_ascribed
                                           uu____5599
                                          in
                                       FStar_Syntax_Syntax.mk uu____5598  in
                                     uu____5591 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let uu____5671 =
                                     let uu____5678 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5678
                                      in
                                   match uu____5671 with
                                   | (top2,c,g_env) ->
                                       let uu____5688 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5688)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5692) ->
           let uu____5739 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5739 with
            | (env0,uu____5753) ->
                let uu____5758 = tc_comp env0 expected_c  in
                (match uu____5758 with
                 | (expected_c1,uu____5772,g) ->
                     let uu____5774 =
                       let uu____5781 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5781 e1  in
                     (match uu____5774 with
                      | (e2,c',g') ->
                          let uu____5791 =
                            let uu____5802 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5802 with
                            | (c'1,g_c') ->
                                let uu____5819 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5819 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____5839 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____5839))
                             in
                          (match uu____5791 with
                           | (e3,expected_c2,g'') ->
                               let uu____5861 = tc_tactic_opt env0 topt  in
                               (match uu____5861 with
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
                                      let uu____5921 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5921
                                       in
                                    let uu____5922 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5922 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5939 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5939
                                            in
                                         let uu____5940 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5940)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5944) ->
           let uu____5991 = FStar_Syntax_Util.type_u ()  in
           (match uu____5991 with
            | (k,u) ->
                let uu____6004 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____6004 with
                 | (t1,uu____6018,f) ->
                     let uu____6020 = tc_tactic_opt env1 topt  in
                     (match uu____6020 with
                      | (topt1,gtac) ->
                          let uu____6039 =
                            let uu____6046 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6046 e1  in
                          (match uu____6039 with
                           | (e2,c,g) ->
                               let uu____6056 =
                                 let uu____6063 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2, ((FStar_Util.Inl t1), topt1),
                                          (FStar_Pervasives_Native.Some
                                             (c.FStar_TypeChecker_Common.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____6063 c
                                  in
                               (match uu____6056 with
                                | (e3,c1,f2) ->
                                    let final_guard =
                                      let uu____6110 =
                                        FStar_TypeChecker_Env.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f
                                        uu____6110
                                       in
                                    let final_guard1 =
                                      wrap_guard_with_tactic_opt topt1
                                        final_guard
                                       in
                                    let uu____6112 =
                                      FStar_TypeChecker_Env.conj_guard
                                        final_guard1 gtac
                                       in
                                    (e3, c1, uu____6112))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6113;
              FStar_Syntax_Syntax.vars = uu____6114;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6193 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6193 with
            | (unary_op1,uu____6217) ->
                let head1 =
                  let uu____6245 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6245
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
              FStar_Syntax_Syntax.pos = uu____6293;
              FStar_Syntax_Syntax.vars = uu____6294;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6373 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6373 with
            | (unary_op1,uu____6397) ->
                let head1 =
                  let uu____6425 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6425
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
                (FStar_Const.Const_reflect uu____6473);
              FStar_Syntax_Syntax.pos = uu____6474;
              FStar_Syntax_Syntax.vars = uu____6475;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6554 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6554 with
            | (unary_op1,uu____6578) ->
                let head1 =
                  let uu____6606 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6606
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
              FStar_Syntax_Syntax.pos = uu____6654;
              FStar_Syntax_Syntax.vars = uu____6655;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6751 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6751 with
            | (unary_op1,uu____6775) ->
                let head1 =
                  let uu____6803 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____6803
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
              FStar_Syntax_Syntax.pos = uu____6859;
              FStar_Syntax_Syntax.vars = uu____6860;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6898 =
             let uu____6905 =
               let uu____6906 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6906  in
             tc_term uu____6905 e1  in
           (match uu____6898 with
            | (e2,c,g) ->
                let uu____6930 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6930 with
                 | (head1,uu____6954) ->
                     let uu____6979 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7012 =
                       let uu____7013 =
                         let uu____7014 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7014  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7013
                        in
                     (uu____6979, uu____7012, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7015;
              FStar_Syntax_Syntax.vars = uu____7016;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7069 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7069 with
            | (head1,uu____7093) ->
                let env' =
                  let uu____7119 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7119  in
                let uu____7120 = tc_term env' r  in
                (match uu____7120 with
                 | (er,uu____7134,gr) ->
                     let uu____7136 = tc_term env1 t  in
                     (match uu____7136 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____7153 =
                            let uu____7154 =
                              let uu____7159 =
                                let uu____7160 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____7169 =
                                  let uu____7180 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____7180]  in
                                uu____7160 :: uu____7169  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____7159
                               in
                            uu____7154 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7153, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7213;
              FStar_Syntax_Syntax.vars = uu____7214;_},uu____7215)
           ->
           let uu____7240 =
             let uu____7246 =
               let uu____7248 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7248  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7246)  in
           FStar_Errors.raise_error uu____7240 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7258;
              FStar_Syntax_Syntax.vars = uu____7259;_},uu____7260)
           ->
           let uu____7285 =
             let uu____7291 =
               let uu____7293 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7293  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7291)  in
           FStar_Errors.raise_error uu____7285 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7303;
              FStar_Syntax_Syntax.vars = uu____7304;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7351 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7351 with
             | (env0,uu____7365) ->
                 let uu____7370 = tc_term env0 e1  in
                 (match uu____7370 with
                  | (e2,c,g) ->
                      let uu____7386 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7386 with
                       | (reify_op,uu____7410) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7436 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7436 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7451 =
                                    let uu____7453 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7453  in
                                  if uu____7451
                                  then
                                    let uu____7456 =
                                      let uu____7462 =
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          ef.FStar_Ident.str
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7462)
                                       in
                                    FStar_Errors.raise_error uu____7456
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
                                    let uu____7505 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7508 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7508
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7505
                                    then
                                      let uu____7511 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7511
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
                                       let uu____7523 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7523
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7524 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7524 with
                                  | (e4,c3,g') ->
                                      let uu____7540 =
                                        let uu____7541 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7541
                                         in
                                      (e4, c3, uu____7540))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7543;
              FStar_Syntax_Syntax.vars = uu____7544;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7592 =
               let uu____7594 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7594  in
             if uu____7592
             then
               let uu____7597 =
                 let uu____7603 =
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7603)  in
               FStar_Errors.raise_error uu____7597 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7609 = FStar_Syntax_Util.head_and_args top  in
             match uu____7609 with
             | (reflect_op,uu____7633) ->
                 let uu____7658 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7658 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7679 =
                        let uu____7685 =
                          let uu____7687 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7687
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7685)  in
                      FStar_Errors.raise_error uu____7679
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7709 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7709 with
                       | (env_no_ex,uu____7723) ->
                           let uu____7728 =
                             let uu____7737 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7737 with
                             | (e2,c,g) ->
                                 ((let uu____7756 =
                                     let uu____7758 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7758
                                      in
                                   if uu____7756
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7728 with
                            | (e2,c_e,g_e) ->
                                let uu____7796 =
                                  let uu____7811 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____7811 with
                                  | (a,u_a) ->
                                      let uu____7832 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____7832 with
                                       | (a_uvar,uu____7861,g_a) ->
                                           let uu____7875 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____7875, u_a, a_uvar, g_a))
                                   in
                                (match uu____7796 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____7917 =
                                         let uu____7918 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____7918.FStar_Syntax_Syntax.n  in
                                       match uu____7917 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7931,uu____7932::args) ->
                                           args
                                       | uu____7974 ->
                                           let uu____7975 =
                                             let uu____7981 =
                                               let uu____7983 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____7985 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____7987 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7983 uu____7985
                                                 uu____7987
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7981)
                                              in
                                           FStar_Errors.raise_error
                                             uu____7975
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8002 =
                                         FStar_Syntax_Syntax.mk_Comp
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [u_a];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               a;
                                             FStar_Syntax_Syntax.effect_args
                                               = eff_args;
                                             FStar_Syntax_Syntax.flags = []
                                           }
                                          in
                                       FStar_All.pipe_right uu____8002
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8038 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8038 with
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
                                          let uu____8061 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8061))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8100 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8100 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____8150,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____8151))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8204 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8204 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8279 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8489 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8279 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8608 =
               let uu____8609 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8609 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8608 instantiate_both  in
           ((let uu____8625 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8625
             then
               let uu____8628 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8630 = FStar_Syntax_Print.term_to_string top  in
               let uu____8632 =
                 let uu____8634 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8634
                   (fun uu___3_8641  ->
                      match uu___3_8641 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8628
                 uu____8630 uu____8632
             else ());
            (let uu____8650 = tc_term (no_inst env2) head1  in
             match uu____8650 with
             | (head2,chead,g_head) ->
                 let uu____8666 =
                   let uu____8671 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8671
                     (fun uu____8688  ->
                        match uu____8688 with
                        | (c,g) ->
                            let uu____8699 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8699))
                    in
                 (match uu____8666 with
                  | (chead1,g_head1) ->
                      let uu____8708 =
                        let uu____8715 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8718 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8718))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head2)
                           in
                        if uu____8715
                        then
                          let uu____8727 =
                            let uu____8734 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head2 chead1
                              g_head1 args uu____8734
                             in
                          match uu____8727 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8748 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head2 chead1 g_head1
                             args uu____8748)
                         in
                      (match uu____8708 with
                       | (e1,c,g) ->
                           let uu____8760 =
                             let uu____8767 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8767
                             then
                               let uu____8776 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8776 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8792 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8792, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8760 with
                            | (e2,c1,implicits) ->
                                ((let uu____8805 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8805
                                  then
                                    let uu____8808 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8808
                                  else ());
                                 (let uu____8813 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8813 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8832 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8832
                                        then
                                          let uu____8835 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8837 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8835 uu____8837
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8842 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8865;
                FStar_Syntax_Syntax.lbunivs = uu____8866;
                FStar_Syntax_Syntax.lbtyp = uu____8867;
                FStar_Syntax_Syntax.lbeff = uu____8868;
                FStar_Syntax_Syntax.lbdef = uu____8869;
                FStar_Syntax_Syntax.lbattrs = uu____8870;
                FStar_Syntax_Syntax.lbpos = uu____8871;_}::[]),uu____8872)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____8898),uu____8899) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8917;
                FStar_Syntax_Syntax.lbunivs = uu____8918;
                FStar_Syntax_Syntax.lbtyp = uu____8919;
                FStar_Syntax_Syntax.lbeff = uu____8920;
                FStar_Syntax_Syntax.lbdef = uu____8921;
                FStar_Syntax_Syntax.lbattrs = uu____8922;
                FStar_Syntax_Syntax.lbpos = uu____8923;_}::uu____8924),uu____8925)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____8953),uu____8954) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____8980 =
        let uu____8981 = FStar_Syntax_Subst.compress top  in
        uu____8981.FStar_Syntax_Syntax.n  in
      match uu____8980 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9028 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9028 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9048 = tc_term env11 e1  in
               (match uu____9048 with
                | (e11,c1,g1) ->
                    let uu____9064 =
                      let uu____9075 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9075 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9064 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9130 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9144 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9144 with
                                | (k,uu____9156) ->
                                    let uu____9157 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9157 with
                                     | (res_t,uu____9178,g) ->
                                         let uu____9192 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9193 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9192, res_t, uu____9193)))
                            in
                         (match uu____9130 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9204 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9204
                                then
                                  let uu____9207 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9207
                                else ());
                               (let guard_x =
                                  FStar_Syntax_Syntax.new_bv
                                    (FStar_Pervasives_Native.Some
                                       (e12.FStar_Syntax_Syntax.pos))
                                    c11.FStar_TypeChecker_Common.res_typ
                                   in
                                let t_eqns =
                                  FStar_All.pipe_right eqns2
                                    (FStar_List.map
                                       (tc_eqn guard_x env_branches))
                                   in
                                let uu____9315 =
                                  let uu____9323 =
                                    FStar_List.fold_right
                                      (fun uu____9416  ->
                                         fun uu____9417  ->
                                           match (uu____9416, uu____9417)
                                           with
                                           | ((branch1,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable1)) ->
                                               let uu____9689 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9689,
                                                 (erasable1 ||
                                                    erasable_branch))) t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9323 with
                                  | (cases,g,erasable1) ->
                                      let uu____9803 =
                                        let uu____9804 =
                                          let uu____9805 =
                                            let uu____9806 =
                                              FStar_All.pipe_right guard_x
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            [uu____9806]  in
                                          FStar_TypeChecker_Env.push_binders
                                            env uu____9805
                                           in
                                        FStar_TypeChecker_Util.bind_cases
                                          uu____9804 res_t cases
                                         in
                                      (uu____9803, g, erasable1)
                                   in
                                match uu____9315 with
                                | (c_branches,g_branches,erasable1) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches)
                                       in
                                    let cres1 =
                                      if erasable1
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool  in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero)
                                           in
                                        let uu____9850 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9850
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9992  ->
                                                  match uu____9992 with
                                                  | ((pat,wopt,br),uu____10040,eff_label,uu____10042,uu____10043,uu____10044,uu____10045)
                                                      ->
                                                      let uu____10084 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10084)))
                                           in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
                                            FStar_Pervasives_Native.None
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let e2 =
                                          FStar_TypeChecker_Util.maybe_monadic
                                            env e
                                            cres1.FStar_TypeChecker_Common.eff_name
                                            cres1.FStar_TypeChecker_Common.res_typ
                                           in
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl
                                                   (cres1.FStar_TypeChecker_Common.res_typ)),
                                                 FStar_Pervasives_Native.None),
                                               (FStar_Pervasives_Native.Some
                                                  (cres1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          e2.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10151 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10151
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10159 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10159  in
                                         let lb =
                                           let uu____10163 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10163 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10169 =
                                             let uu____10176 =
                                               let uu____10177 =
                                                 let uu____10191 =
                                                   let uu____10194 =
                                                     let uu____10195 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         guard_x
                                                        in
                                                     [uu____10195]  in
                                                   FStar_Syntax_Subst.close
                                                     uu____10194 e_match
                                                    in
                                                 ((false, [lb]), uu____10191)
                                                  in
                                               FStar_Syntax_Syntax.Tm_let
                                                 uu____10177
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10176
                                              in
                                           uu____10169
                                             FStar_Pervasives_Native.None
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10228 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10228
                                      then
                                        let uu____10231 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10233 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10231 uu____10233
                                      else ());
                                     (let uu____10238 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10238)))))))))
      | uu____10239 ->
          let uu____10240 =
            let uu____10242 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10242  in
          failwith uu____10240

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
          let uu____10267 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10306))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10347 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10267 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10380 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10380 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10384 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10384)
                 in
              let uu____10387 =
                let uu____10394 =
                  let uu____10395 =
                    let uu____10396 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10396
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10395  in
                tc_term uu____10394 typ  in
              (match uu____10387 with
               | (typ1,uu____10412,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10415 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10415 with
                     | (tau1,uu____10429,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1320_10434 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1320_10434.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1320_10434.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10436 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10436
                            then
                              let uu____10441 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10441
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10447 =
                              let uu____10448 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10448
                               in
                            (t, uu____10447,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun a  ->
    fun b  ->
      fun env  ->
        fun tau  ->
          let env1 =
            let uu___1330_10454 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1330_10454.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1330_10454.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1330_10454.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1330_10454.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1330_10454.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1330_10454.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1330_10454.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1330_10454.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1330_10454.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1330_10454.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1330_10454.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1330_10454.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1330_10454.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1330_10454.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1330_10454.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1330_10454.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1330_10454.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___1330_10454.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1330_10454.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1330_10454.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1330_10454.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1330_10454.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1330_10454.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1330_10454.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1330_10454.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1330_10454.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1330_10454.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1330_10454.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1330_10454.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1330_10454.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1330_10454.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1330_10454.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1330_10454.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1330_10454.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1330_10454.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1330_10454.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1330_10454.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1330_10454.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1330_10454.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1330_10454.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1330_10454.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1330_10454.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1330_10454.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1330_10454.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____10456 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10456

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
          let uu____10478 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10478 with
           | (tactic1,uu____10492,g) ->
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
        let uu____10544 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____10544 with
        | (e2,t,implicits) ->
            let tc =
              let uu____10565 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10565
              then FStar_Util.Inl t
              else
                (let uu____10574 =
                   let uu____10575 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10575
                    in
                 FStar_Util.Inr uu____10574)
               in
            let is_data_ctor uu___4_10584 =
              match uu___4_10584 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10589) -> true
              | uu____10597 -> false  in
            let uu____10601 =
              (is_data_ctor dc) &&
                (let uu____10604 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10604)
               in
            if uu____10601
            then
              let uu____10613 =
                let uu____10619 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10619)  in
              let uu____10623 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10613 uu____10623
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10641 =
            let uu____10647 =
              let uu____10649 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10649
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10647)  in
          FStar_Errors.raise_error uu____10641 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10677 =
            let uu____10682 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10682  in
          value_check_expected_typ env1 e uu____10677
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10684 =
            let uu____10697 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10697 with
            | FStar_Pervasives_Native.None  ->
                let uu____10712 = FStar_Syntax_Util.type_u ()  in
                (match uu____10712 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10684 with
           | (t,uu____10750,g0) ->
               let uu____10764 =
                 let uu____10777 =
                   let uu____10779 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____10779
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____10777 r env1 t
                  in
               (match uu____10764 with
                | (e1,uu____10789,g1) ->
                    let uu____10803 =
                      let uu____10804 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10804
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10805 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10803, uu____10805)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10807 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10817 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____10817)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10807 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1395_10831 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1395_10831.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1395_10831.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____10834 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____10834 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____10855 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____10855
                       then FStar_Util.Inl t1
                       else
                         (let uu____10864 =
                            let uu____10865 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10865
                             in
                          FStar_Util.Inr uu____10864)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10867;
             FStar_Syntax_Syntax.vars = uu____10868;_},uu____10869)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10874 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10874
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10884 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10884
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10894;
             FStar_Syntax_Syntax.vars = uu____10895;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____10904 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10904 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10928 =
                     let uu____10934 =
                       let uu____10936 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____10938 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____10940 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10936 uu____10938 uu____10940
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10934)
                      in
                   let uu____10944 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____10928 uu____10944)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10961 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10966 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10966 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10968 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10968 with
           | ((us,t),range) ->
               ((let uu____10991 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____10991
                 then
                   let uu____10996 =
                     let uu____10998 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____10998  in
                   let uu____10999 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____11001 = FStar_Range.string_of_range range  in
                   let uu____11003 = FStar_Range.string_of_use_range range
                      in
                   let uu____11005 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10996 uu____10999 uu____11001 uu____11003
                     uu____11005
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____11013 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____11013 us  in
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
          let uu____11041 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____11041 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____11055 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11055 with
                | (env2,uu____11069) ->
                    let uu____11074 = tc_binders env2 bs1  in
                    (match uu____11074 with
                     | (bs2,env3,g,us) ->
                         let uu____11093 = tc_comp env3 c1  in
                         (match uu____11093 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1475_11112 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1475_11112.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1475_11112.FStar_Syntax_Syntax.vars)
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
                                  let uu____11123 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____11123
                                   in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 false bs2 g1
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
          let uu____11140 =
            let uu____11145 =
              let uu____11146 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11146]  in
            FStar_Syntax_Subst.open_term uu____11145 phi  in
          (match uu____11140 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____11174 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11174 with
                | (env2,uu____11188) ->
                    let uu____11193 =
                      let uu____11208 = FStar_List.hd x1  in
                      tc_binder env2 uu____11208  in
                    (match uu____11193 with
                     | (x2,env3,f1,u) ->
                         ((let uu____11244 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____11244
                           then
                             let uu____11247 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____11249 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11251 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____11247 uu____11249 uu____11251
                           else ());
                          (let uu____11258 = FStar_Syntax_Util.type_u ()  in
                           match uu____11258 with
                           | (t_phi,uu____11270) ->
                               let uu____11271 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____11271 with
                                | (phi2,uu____11285,f2) ->
                                    let e1 =
                                      let uu___1513_11290 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1513_11290.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1513_11290.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____11299 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____11299
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11328) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____11355 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____11355
            then
              let uu____11358 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1526_11362 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1526_11362.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1526_11362.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11358
            else ());
           (let uu____11378 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____11378 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____11391 ->
          let uu____11392 =
            let uu____11394 = FStar_Syntax_Print.term_to_string top  in
            let uu____11396 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11394
              uu____11396
             in
          failwith uu____11392

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____11408 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____11410,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____11423,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____11441 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____11447 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____11449 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____11450 ->
            let uu____11452 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____11452 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____11457 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____11458 =
              let uu____11464 =
                let uu____11466 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11466
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11464)  in
            FStar_Errors.raise_error uu____11458 r
        | FStar_Const.Const_set_range_of  ->
            let uu____11470 =
              let uu____11476 =
                let uu____11478 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11478
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11476)  in
            FStar_Errors.raise_error uu____11470 r
        | FStar_Const.Const_reify  ->
            let uu____11482 =
              let uu____11488 =
                let uu____11490 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11490
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11488)  in
            FStar_Errors.raise_error uu____11482 r
        | FStar_Const.Const_reflect uu____11494 ->
            let uu____11495 =
              let uu____11501 =
                let uu____11503 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11503
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11501)  in
            FStar_Errors.raise_error uu____11495 r
        | uu____11507 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____11526) ->
          let uu____11535 = FStar_Syntax_Util.type_u ()  in
          (match uu____11535 with
           | (k,u) ->
               let uu____11548 = tc_check_tot_or_gtot_term env t k  in
               (match uu____11548 with
                | (t1,uu____11562,g) ->
                    let uu____11564 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11564, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____11566) ->
          let uu____11575 = FStar_Syntax_Util.type_u ()  in
          (match uu____11575 with
           | (k,u) ->
               let uu____11588 = tc_check_tot_or_gtot_term env t k  in
               (match uu____11588 with
                | (t1,uu____11602,g) ->
                    let uu____11604 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11604, u, g)))
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
            let uu____11614 =
              let uu____11619 =
                let uu____11620 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____11620 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____11619  in
            uu____11614 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11637 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____11637 with
           | (tc1,uu____11651,f) ->
               let uu____11653 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11653 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____11703 =
                        let uu____11704 = FStar_Syntax_Subst.compress head3
                           in
                        uu____11704.FStar_Syntax_Syntax.n  in
                      match uu____11703 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11707,us) -> us
                      | uu____11713 -> []  in
                    let uu____11714 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____11714 with
                     | (uu____11737,args1) ->
                         let uu____11763 =
                           let uu____11786 = FStar_List.hd args1  in
                           let uu____11803 = FStar_List.tl args1  in
                           (uu____11786, uu____11803)  in
                         (match uu____11763 with
                          | (res,args2) ->
                              let uu____11884 =
                                let uu____11893 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11921  ->
                                          match uu___5_11921 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11929 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____11929 with
                                               | (env1,uu____11941) ->
                                                   let uu____11946 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____11946 with
                                                    | (e1,uu____11958,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____11893
                                  FStar_List.unzip
                                 in
                              (match uu____11884 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1655_11999 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1655_11999.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags = flags
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____12005 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____12005))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____12015 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____12019 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____12029 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____12029
        | FStar_Syntax_Syntax.U_max us ->
            let uu____12033 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____12033
        | FStar_Syntax_Syntax.U_name x ->
            let uu____12037 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____12037
            then u2
            else
              (let uu____12042 =
                 let uu____12044 =
                   let uu____12046 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____12046 " not found"  in
                 Prims.op_Hat "Universe variable " uu____12044  in
               failwith uu____12042)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____12053 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____12053 FStar_Pervasives_Native.snd
         | uu____12062 -> aux u)

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
            let uu____12093 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____12093 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____12182 bs2 bs_expected1 =
              match uu____12182 with
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
                              uu____12373),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12374)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____12389),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12390)) -> true
                           | uu____12399 -> false  in
                         let uu____12409 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____12412 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____12412 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____12409
                         then
                           let uu____12414 =
                             let uu____12420 =
                               let uu____12422 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____12422
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____12420)
                              in
                           let uu____12426 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____12414 uu____12426
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____12430 =
                           let uu____12437 =
                             let uu____12438 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____12438.FStar_Syntax_Syntax.n  in
                           match uu____12437 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12449 ->
                               ((let uu____12451 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____12451
                                 then
                                   let uu____12454 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____12454
                                 else ());
                                (let uu____12459 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____12459 with
                                 | (t,uu____12473,g1_env) ->
                                     let g2_env =
                                       let uu____12476 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       match uu____12476 with
                                       | FStar_Pervasives_Native.Some g ->
                                           FStar_All.pipe_right g
                                             (FStar_TypeChecker_Rel.resolve_implicits
                                                env2)
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____12480 =
                                             FStar_TypeChecker_Rel.get_subtyping_prop
                                               env2 expected_t t
                                              in
                                           (match uu____12480 with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____12483 =
                                                  FStar_TypeChecker_Err.basic_type_error
                                                    env2
                                                    FStar_Pervasives_Native.None
                                                    expected_t t
                                                   in
                                                let uu____12489 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____12483 uu____12489
                                            | FStar_Pervasives_Native.Some
                                                g_env ->
                                                FStar_TypeChecker_Util.label_guard
                                                  (hd1.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                  "Type annotation on parameter incompatible with the expected type"
                                                  g_env)
                                        in
                                     let uu____12492 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____12492)))
                            in
                         match uu____12430 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1755_12518 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1755_12518.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1755_12518.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____12541 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____12541
                                in
                             let uu____12544 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____12544 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____12609 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____12609,
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
                  | uu____12781 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____12791 = tc_binders env1 bs  in
                  match uu____12791 with
                  | (bs1,envbody,g_env,uu____12821) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____12877 =
                    let uu____12878 = FStar_Syntax_Subst.compress t2  in
                    uu____12878.FStar_Syntax_Syntax.n  in
                  match uu____12877 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____12911 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12931 -> failwith "Impossible");
                       (let uu____12941 = tc_binders env1 bs  in
                        match uu____12941 with
                        | (bs1,envbody,g_env,uu____12983) ->
                            let uu____12984 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12984 with
                             | (envbody1,uu____13022) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____13043;
                         FStar_Syntax_Syntax.pos = uu____13044;
                         FStar_Syntax_Syntax.vars = uu____13045;_},uu____13046)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____13090 -> failwith "Impossible");
                       (let uu____13100 = tc_binders env1 bs  in
                        match uu____13100 with
                        | (bs1,envbody,g_env,uu____13142) ->
                            let uu____13143 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13143 with
                             | (envbody1,uu____13181) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____13203) ->
                      let uu____13208 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____13208 with
                       | (uu____13269,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____13346 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____13346 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____13491 c_expected2
                               body3 =
                               match uu____13491 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____13605 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____13605,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____13622 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____13622
                                           in
                                        let uu____13623 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____13623,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____13640 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____13640
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
                                               let uu____13706 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____13706 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____13733 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____13733 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____13788 =
                                                           let uu____13815 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____13815,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____13788
                                                           c_expected4 body3))
                                           | uu____13838 ->
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
                             let uu____13867 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____13867 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1881_13932 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1881_13932.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1881_13932.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1881_13932.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1881_13932.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1881_13932.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1881_13932.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1881_13932.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1881_13932.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1881_13932.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1881_13932.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1881_13932.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1881_13932.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1881_13932.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1881_13932.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1881_13932.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1881_13932.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1881_13932.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1881_13932.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1881_13932.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1881_13932.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1881_13932.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1881_13932.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1881_13932.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1881_13932.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1881_13932.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1881_13932.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1881_13932.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1881_13932.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1881_13932.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1881_13932.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1881_13932.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1881_13932.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1881_13932.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1881_13932.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1881_13932.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___1881_13932.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1881_13932.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1881_13932.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1881_13932.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1881_13932.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1881_13932.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1881_13932.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1881_13932.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___1881_13932.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             let uu____13939 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____14005  ->
                                       fun uu____14006  ->
                                         match (uu____14005, uu____14006)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____14097 =
                                               let uu____14104 =
                                                 let uu____14105 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____14105
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____14104 t3  in
                                             (match uu____14097 with
                                              | (t4,uu____14129,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____14142 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1899_14145
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1899_14145.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1899_14145.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____14142 ::
                                                          letrec_binders
                                                    | uu____14146 ->
                                                        letrec_binders
                                                     in
                                                  let uu____14151 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____14151)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____13939 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____14171 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____14171)
                              in
                           let uu____14174 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____14174 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____14250 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____14250 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____14297 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____14297))))
                  | uu____14314 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____14346 =
                          let uu____14347 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____14347
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____14346
                      else
                        (let uu____14351 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____14351 with
                         | (uu____14400,bs1,uu____14402,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14434 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14434 with
          | (env1,topt) ->
              ((let uu____14454 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14454
                then
                  let uu____14457 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14457
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14471 = expected_function_typ1 env1 topt body  in
                match uu____14471 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14512 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14512
                      then
                        let uu____14515 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14520 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14525 =
                          let uu____14527 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14527 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14515 uu____14520 uu____14525
                      else ());
                     (let uu____14537 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14537
                      then
                        let uu____14542 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14545 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14542 uu____14545
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14551 =
                        let should_check_expected_effect =
                          let uu____14564 =
                            let uu____14571 =
                              let uu____14572 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____14572.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____14571)  in
                          match uu____14564 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____14578,(FStar_Util.Inr
                                           expected_c,uu____14580),uu____14581))
                              -> false
                          | uu____14631 -> true  in
                        let uu____14639 =
                          tc_term
                            (let uu___1972_14648 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1972_14648.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1972_14648.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1972_14648.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1972_14648.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1972_14648.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1972_14648.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1972_14648.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1972_14648.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1972_14648.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1972_14648.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1972_14648.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1972_14648.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1972_14648.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1972_14648.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1972_14648.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1972_14648.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1972_14648.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1972_14648.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1972_14648.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1972_14648.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1972_14648.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1972_14648.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1972_14648.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1972_14648.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1972_14648.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1972_14648.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1972_14648.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1972_14648.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1972_14648.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1972_14648.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1972_14648.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1972_14648.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1972_14648.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1972_14648.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1972_14648.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1972_14648.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1972_14648.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1972_14648.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1972_14648.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1972_14648.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1972_14648.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1972_14648.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1972_14648.FStar_TypeChecker_Env.erasable_types_tab)
                             }) body1
                           in
                        match uu____14639 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____14675 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____14675 with
                               | (cbody1,g_lc) ->
                                   let uu____14692 =
                                     check_expected_effect
                                       (let uu___1983_14701 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___1983_14701.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___1983_14701.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___1983_14701.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___1983_14701.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___1983_14701.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___1983_14701.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___1983_14701.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___1983_14701.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___1983_14701.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___1983_14701.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___1983_14701.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___1983_14701.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___1983_14701.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___1983_14701.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___1983_14701.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___1983_14701.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___1983_14701.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___1983_14701.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___1983_14701.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___1983_14701.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___1983_14701.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___1983_14701.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___1983_14701.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___1983_14701.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___1983_14701.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___1983_14701.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___1983_14701.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___1983_14701.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___1983_14701.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___1983_14701.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___1983_14701.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___1983_14701.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____14692 with
                                    | (body3,cbody2,guard) ->
                                        let uu____14715 =
                                          let uu____14716 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____14716
                                           in
                                        (body3, cbody2, uu____14715)))
                            else
                              (let uu____14723 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____14723 with
                               | (cbody1,g_lc) ->
                                   let uu____14740 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____14740))
                         in
                      match uu____14551 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14763 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14766 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14766)
                               in
                            if uu____14763
                            then
                              let uu____14769 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14770 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14769
                                uu____14770
                            else
                              (let guard =
                                 let uu____14774 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14774
                                  in
                               guard)
                             in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              false bs1 guard
                             in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody  in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt)))
                             in
                          let uu____14789 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14813
                                     -> (e, t_annot, guard1)
                                 | uu____14828 ->
                                     let lc =
                                       let uu____14830 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____14830
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____14831 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e lc t1
                                        in
                                     (match uu____14831 with
                                      | (e1,uu____14845,guard') ->
                                          let uu____14847 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____14847)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____14789 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____14858 =
                                 let uu____14863 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14863 guard2
                                  in
                               (match uu____14858 with
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
              (let uu____14914 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____14914
               then
                 let uu____14917 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____14919 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14917
                   uu____14919
               else ());
              (let monadic_application uu____15001 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____15001 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____15070 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____15070 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____15084 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____15100 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____15100
                                   in
                                (cres1, g)
                            | uu____15101 ->
                                let g =
                                  let uu____15111 =
                                    let uu____15112 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____15112
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____15111
                                   in
                                let uu____15113 =
                                  let uu____15114 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____15114
                                   in
                                (uu____15113, g)
                             in
                          (match uu____15084 with
                           | (cres2,guard1) ->
                               ((let uu____15124 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____15124
                                 then
                                   let uu____15127 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____15127
                                 else ());
                                (let uu____15132 =
                                   let uu____15137 =
                                     let uu____15138 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____15138
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____15139 =
                                     let uu____15140 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____15140
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____15137, uu____15139)  in
                                 match uu____15132 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15164  ->
                                                 match uu____15164 with
                                                 | (uu____15174,uu____15175,lc)
                                                     ->
                                                     (let uu____15183 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15183)
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
                                       let uu____15196 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15196
                                       then
                                         ((let uu____15200 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15200
                                           then
                                             let uu____15203 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15203
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15211 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15211
                                           then
                                             let uu____15214 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15214
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15245  ->
                                              match uu____15245 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15287 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15287
                                                    then
                                                      let uu____15290 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15295 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15297 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15290
                                                        uu____15295
                                                        uu____15297
                                                    else ());
                                                   (let uu____15302 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15302
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
                                       (let uu____15313 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15313
                                        then
                                          let uu____15316 =
                                            FStar_Syntax_Print.term_to_string
                                              head2
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15316
                                        else ());
                                       (let uu____15321 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15321
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
                                       let uu____15332 =
                                         let uu____15333 =
                                           FStar_Syntax_Subst.compress head2
                                            in
                                         uu____15333.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15332 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15338 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15361  ->
                                                  match uu____15361 with
                                                  | (arg,uu____15375,uu____15376)
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
                                         (let uu____15387 =
                                            let map_fun uu____15449 =
                                              match uu____15449 with
                                              | ((e,q),uu____15490,c) ->
                                                  ((let uu____15513 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15513
                                                    then
                                                      let uu____15516 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15518 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15516
                                                        uu____15518
                                                    else ());
                                                   (let uu____15523 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15523
                                                    then
                                                      ((let uu____15549 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15549
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
                                                           (let uu____15590 =
                                                              let uu____15592
                                                                =
                                                                let uu____15593
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head2
                                                                   in
                                                                uu____15593.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15592
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15598
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15598
                                                              | uu____15600
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15590)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15604 =
                                                            let uu____15610 =
                                                              let uu____15612
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15614
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head2
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15612
                                                                (c.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                                                                uu____15614
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15610)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15604)
                                                       else ();
                                                       (let uu____15621 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15621
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
                                                        let uu____15629 =
                                                          let uu____15638 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15638, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15629)))))
                                               in
                                            let uu____15667 =
                                              let uu____15694 =
                                                let uu____15719 =
                                                  let uu____15730 =
                                                    let uu____15739 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head2
                                                       in
                                                    (uu____15739,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15730 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15719
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15694
                                               in
                                            match uu____15667 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____15912 =
                                                  let uu____15913 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15913
                                                   in
                                                let uu____15934 =
                                                  let uu____15935 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____15935
                                                   in
                                                (lifted_args, uu____15912,
                                                  uu____15934)
                                             in
                                          match uu____15387 with
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
                                                uu___6_16034 =
                                                match uu___6_16034 with
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
                                                      let uu____16095 =
                                                        let uu____16102 =
                                                          let uu____16103 =
                                                            let uu____16117 =
                                                              let uu____16120
                                                                =
                                                                let uu____16121
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____16121]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____16120 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____16117)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____16103
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____16102
                                                         in
                                                      uu____16095
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
                                     let uu____16169 = (comp1, guard1)  in
                                     (match uu____16169 with
                                      | (comp2,g) ->
                                          ((let uu____16183 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16183
                                            then
                                              let uu____16186 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16188 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16186 uu____16188
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16269 bs args1 =
                 match uu____16269 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16408))::rest,
                         (uu____16410,FStar_Pervasives_Native.None )::uu____16411)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16472 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____16472 with
                           | (t1,g_ex) ->
                               let uu____16485 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____16485 with
                                | (varg,uu____16506,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____16534 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16534)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16543 =
                                      let uu____16578 =
                                        let uu____16589 =
                                          let uu____16598 =
                                            let uu____16599 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____16599
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16598)
                                           in
                                        uu____16589 :: outargs  in
                                      (subst2, uu____16578, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16543 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____16645,FStar_Pervasives_Native.None
                                                                 )::uu____16646)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____16708 =
                            tc_tactic FStar_Syntax_Syntax.t_unit
                              FStar_Syntax_Syntax.t_unit env tau1
                             in
                          (match uu____16708 with
                           | (tau2,uu____16722,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16725 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____16725 with
                                | (t1,g_ex) ->
                                    let uu____16738 =
                                      let uu____16751 =
                                        let uu____16758 =
                                          let uu____16763 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____16763, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____16758
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____16751
                                       in
                                    (match uu____16738 with
                                     | (varg,uu____16776,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____16804 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____16804)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____16813 =
                                           let uu____16848 =
                                             let uu____16859 =
                                               let uu____16868 =
                                                 let uu____16869 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____16869
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16868)
                                                in
                                             uu____16859 :: outargs  in
                                           (subst2, uu____16848, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____16813 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16985,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16986)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____16997),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16998)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____17006),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17007)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____17022 ->
                                let uu____17031 =
                                  let uu____17037 =
                                    let uu____17039 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____17041 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____17043 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____17045 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____17039 uu____17041 uu____17043
                                      uu____17045
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____17037)
                                   in
                                FStar_Errors.raise_error uu____17031
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2262_17052 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2262_17052.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2262_17052.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____17054 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____17054
                             then
                               let uu____17057 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____17059 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17061 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17063 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____17065 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____17057 uu____17059 uu____17061
                                 uu____17063 uu____17065
                             else ());
                            (let uu____17070 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____17070 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2271_17085 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2271_17085.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2271_17085.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2271_17085.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2271_17085.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2271_17085.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2271_17085.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2271_17085.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2271_17085.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2271_17085.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2271_17085.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2271_17085.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2271_17085.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2271_17085.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2271_17085.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2271_17085.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2271_17085.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2271_17085.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2271_17085.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2271_17085.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2271_17085.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2271_17085.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2271_17085.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2271_17085.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2271_17085.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2271_17085.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2271_17085.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2271_17085.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2271_17085.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2271_17085.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2271_17085.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2271_17085.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2271_17085.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2271_17085.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2271_17085.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2271_17085.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2271_17085.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2271_17085.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2271_17085.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2271_17085.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2271_17085.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2271_17085.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2271_17085.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2271_17085.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2271_17085.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____17087 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____17087
                                   then
                                     let uu____17090 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____17092 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____17094 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____17090 uu____17092 uu____17094
                                   else ());
                                  (let uu____17099 = tc_term env2 e  in
                                   match uu____17099 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17116 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17116
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17139 =
                                           let uu____17142 =
                                             let uu____17151 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17151
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17142
                                            in
                                         (uu____17139, aq)  in
                                       let uu____17160 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17160
                                       then
                                         let subst2 =
                                           let uu____17170 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____17170 e1
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
                      | (uu____17269,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17305) ->
                          let uu____17356 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____17356 with
                           | (head2,chead1,ghead1) ->
                               let uu____17378 =
                                 let uu____17383 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____17383
                                   (fun uu____17400  ->
                                      match uu____17400 with
                                      | (c,g1) ->
                                          let uu____17411 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____17411))
                                  in
                               (match uu____17378 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17454 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____17454
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____17485 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____17485 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head2, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____17508 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____17508
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
                                      | uu____17555 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17563 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____17563
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____17564 =
                                              let uu____17565 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____17565.FStar_Syntax_Syntax.n
                                               in
                                            match uu____17564 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17568;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17569;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____17571)
                                                -> norm_tres tres4
                                            | uu____17579 -> tres3  in
                                          let uu____17580 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____17580
                                      | uu____17582 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____17585 ->
                                          let uu____17586 =
                                            let uu____17592 =
                                              let uu____17594 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____17596 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____17598 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17594 uu____17596
                                                uu____17598
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17592)
                                             in
                                          let uu____17602 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____17586 uu____17602
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____17632 =
                   let uu____17633 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____17633.FStar_Syntax_Syntax.n  in
                 match uu____17632 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17642 ->
                     let uu____17655 =
                       FStar_List.fold_right
                         (fun uu____17686  ->
                            fun uu____17687  ->
                              match uu____17687 with
                              | (bs,guard1) ->
                                  let uu____17714 =
                                    let uu____17727 =
                                      let uu____17728 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17728
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17727
                                     in
                                  (match uu____17714 with
                                   | (t,uu____17745,g) ->
                                       let uu____17759 =
                                         let uu____17762 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17762 :: bs  in
                                       let uu____17763 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17759, uu____17763))) args
                         ([], guard)
                        in
                     (match uu____17655 with
                      | (bs,guard1) ->
                          let uu____17780 =
                            let uu____17787 =
                              let uu____17800 =
                                let uu____17801 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17801
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17800
                               in
                            match uu____17787 with
                            | (t,uu____17818,g) ->
                                let uu____17832 = FStar_Options.ml_ish ()  in
                                if uu____17832
                                then
                                  let uu____17841 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17844 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17841, uu____17844)
                                else
                                  (let uu____17849 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17852 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17849, uu____17852))
                             in
                          (match uu____17780 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17871 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17871
                                 then
                                   let uu____17875 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____17877 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17879 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17875 uu____17877 uu____17879
                                 else ());
                                (let g =
                                   let uu____17885 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17885
                                    in
                                 let uu____17886 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17886))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17887;
                        FStar_Syntax_Syntax.pos = uu____17888;
                        FStar_Syntax_Syntax.vars = uu____17889;_},uu____17890)
                     ->
                     let uu____17927 =
                       FStar_List.fold_right
                         (fun uu____17958  ->
                            fun uu____17959  ->
                              match uu____17959 with
                              | (bs,guard1) ->
                                  let uu____17986 =
                                    let uu____17999 =
                                      let uu____18000 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18000
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17999
                                     in
                                  (match uu____17986 with
                                   | (t,uu____18017,g) ->
                                       let uu____18031 =
                                         let uu____18034 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18034 :: bs  in
                                       let uu____18035 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18031, uu____18035))) args
                         ([], guard)
                        in
                     (match uu____17927 with
                      | (bs,guard1) ->
                          let uu____18052 =
                            let uu____18059 =
                              let uu____18072 =
                                let uu____18073 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18073
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18072
                               in
                            match uu____18059 with
                            | (t,uu____18090,g) ->
                                let uu____18104 = FStar_Options.ml_ish ()  in
                                if uu____18104
                                then
                                  let uu____18113 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18116 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18113, uu____18116)
                                else
                                  (let uu____18121 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18124 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18121, uu____18124))
                             in
                          (match uu____18052 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18143 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18143
                                 then
                                   let uu____18147 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____18149 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18151 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18147 uu____18149 uu____18151
                                 else ());
                                (let g =
                                   let uu____18157 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18157
                                    in
                                 let uu____18158 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18158))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18181 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18181 with
                      | (bs1,c1) ->
                          let head_info = (head1, chead, ghead, c1)  in
                          ((let uu____18204 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18204
                            then
                              let uu____18207 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____18209 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18211 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18214 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18207 uu____18209 uu____18211
                                uu____18214
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18260) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18266,uu____18267) ->
                     check_function_app t guard
                 | uu____18308 ->
                     let uu____18309 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18309
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
                  let uu____18392 =
                    FStar_List.fold_left2
                      (fun uu____18461  ->
                         fun uu____18462  ->
                           fun uu____18463  ->
                             match (uu____18461, uu____18462, uu____18463)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____18616 =
                                     let uu____18618 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____18618 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____18616
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18624 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____18624 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____18653 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18653 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18658 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____18658)
                                              &&
                                              (let uu____18661 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____18661))
                                          in
                                       let uu____18663 =
                                         let uu____18674 =
                                           let uu____18685 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____18685]  in
                                         FStar_List.append seen uu____18674
                                          in
                                       let uu____18718 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____18663, uu____18718, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____18392 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____18786 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____18786
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____18789 = (c1, guard)  in
                       (match uu____18789 with | (c2,g) -> (e, c2, g)))
              | uu____18802 ->
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
            let uu____18900 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18900 with
            | (head1,args) ->
                let uu____18943 =
                  let uu____18944 = FStar_Syntax_Subst.compress head1  in
                  uu____18944.FStar_Syntax_Syntax.n  in
                (match uu____18943 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18948;
                        FStar_Syntax_Syntax.vars = uu____18949;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18956 ->
                     if norm1
                     then t1
                     else
                       (let uu____18960 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____18960))
          
          and unfold_once t f us args =
            let uu____18978 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____18978
            then t
            else
              (let uu____18983 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____18983 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____19003 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____19003 with
                    | (uu____19008,head_def) ->
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
          let uu____19015 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____19015  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____19034 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19034
           then
             let uu____19039 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____19041 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____19039 uu____19041
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____19061 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____19063 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____19061 uu____19063 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____19067 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____19067 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19111 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19111 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19112;
                    FStar_Syntax_Syntax.pos = uu____19113;
                    FStar_Syntax_Syntax.vars = uu____19114;_} ->
                    let uu____19117 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19117 with
                     | (head_p,args_p) ->
                         let uu____19160 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19160
                         then
                           let uu____19163 =
                             let uu____19164 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19164.FStar_Syntax_Syntax.n  in
                           (match uu____19163 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19169 =
                                    let uu____19171 =
                                      let uu____19173 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19173
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19171
                                     in
                                  if uu____19169
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____19201 =
                                    let uu____19226 =
                                      let uu____19230 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19230
                                       in
                                    match uu____19226 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____19279 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____19279 with
                                         | (params_p,uu____19337) ->
                                             let uu____19378 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____19378 with
                                              | (params_s,uu____19436) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19201 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____19565  ->
                                             fun uu____19566  ->
                                               match (uu____19565,
                                                       uu____19566)
                                               with
                                               | ((p,uu____19600),(s,uu____19602))
                                                   ->
                                                   let uu____19635 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____19635 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____19638 =
                                                          let uu____19640 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____19642 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19640
                                                            uu____19642
                                                           in
                                                        fail2 uu____19638
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
                            | uu____19647 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____19651 =
                              let uu____19653 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____19655 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19653 uu____19655
                               in
                            fail2 uu____19651))
                | uu____19658 ->
                    let uu____19659 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____19659 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____19702 = FStar_Syntax_Util.head_and_args e  in
          match uu____19702 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19772 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____19772 with
                    | (us,t_f) ->
                        let uu____19792 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____19792 with
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
                              (let rec aux uu____19929 formals1 args1 =
                                 match uu____19929 with
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
                                          let uu____20080 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____20080, bvs, guard,
                                            erasable1)
                                      | ((f1,uu____20087)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____20145 =
                                            let uu____20166 =
                                              let uu____20167 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____20167.FStar_Syntax_Syntax.n
                                               in
                                            match uu____20166 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2578_20192 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2578_20192.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2578_20192.FStar_Syntax_Syntax.index);
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
                                                uu____20215 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____20229 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____20229 with
                                                 | (a1,uu____20257,g) ->
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
                                            | uu____20281 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____20145 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____20346 =
                                                 let uu____20369 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20369)
                                                  in
                                               aux uu____20346 formals2 args2)
                                      | uu____20408 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20467 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____20533 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____20533
           then
             let uu____20538 = FStar_Syntax_Print.pat_to_string p  in
             let uu____20540 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20538
               uu____20540
           else ());
          (let id1 =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20565 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____20565 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____20576 =
                 let uu____20581 =
                   let uu____20582 =
                     let uu____20591 =
                       let uu____20592 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____20592
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____20591
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____20582]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____20581  in
               uu____20576 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____20628 =
                 let uu____20633 =
                   let uu____20634 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____20634]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20633  in
               uu____20628 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20696 ->
               let uu____20703 =
                 let uu____20705 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20705
                  in
               failwith uu____20703
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2617_20727 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2617_20727.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2617_20727.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20728 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____20728,
                 (let uu___2620_20735 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2620_20735.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2624_20739 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2624_20739.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2624_20739.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20740 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____20740,
                 (let uu___2627_20747 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2627_20747.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____20749 ->
               let uu____20750 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____20750 with
                | (uu____20779,e_c,uu____20781,uu____20782) ->
                    let uu____20787 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____20787 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____20817 =
                              let uu____20819 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____20819  in
                            if uu____20817
                            then
                              let uu____20822 =
                                let uu____20824 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____20826 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20824 uu____20826
                                 in
                              fail1 uu____20822
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20888  ->
                        match uu____20888 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20918
                                 -> (p1, b)
                             | uu____20928 ->
                                 let uu____20929 =
                                   let uu____20932 =
                                     let uu____20933 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____20933
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____20932
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____20929, b))) sub_pats
                    in
                 let uu___2655_20937 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2655_20937.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20982  ->
                         match uu____20982 with
                         | (x,uu____20992) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____21000
                                  -> false
                              | uu____21008 -> true)))
                  in
               let uu____21010 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____21010 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____21054 =
                          let uu____21056 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____21058 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____21060 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____21067 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____21056 uu____21058 uu____21060 uu____21067
                           in
                        failwith uu____21054)
                     else ();
                     (let uu____21072 =
                        let uu____21084 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____21084 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable1)
                            ->
                            let g' =
                              let uu____21121 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21121  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21124 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21124
                              then
                                let uu____21129 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21131 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21133 =
                                  let uu____21135 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21143 =
                                           let uu____21145 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21147 =
                                             let uu____21149 =
                                               let uu____21151 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21151 ")"
                                                in
                                             Prims.op_Hat " : " uu____21149
                                              in
                                           Prims.op_Hat uu____21145
                                             uu____21147
                                            in
                                         Prims.op_Hat "(" uu____21143)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21135
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21129 uu____21131 uu____21133
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable1))
                         in
                      match uu____21072 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable1) ->
                          let uu____21194 =
                            let uu____21226 =
                              let uu____21258 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21258, erasable1,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21340  ->
                                 fun uu____21341  ->
                                   fun x  ->
                                     match (uu____21340, uu____21341) with
                                     | ((env2,bvs,tms,pats,subst1,g,erasable2,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____21525 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____21525 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21595 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21595 i
                                                   in
                                                let uu____21596 =
                                                  let uu____21605 =
                                                    let uu____21610 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____21610  in
                                                  FStar_List.map uu____21605
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____21596
                                                 in
                                              let uu____21616 =
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
                                                uu____21616,
                                                (erasable2 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21226 sub_pats1 simple_bvs1
                             in
                          (match uu____21194 with
                           | (_env,bvs,tms,checked_sub_pats,subst1,g,erasable2,uu____21675)
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
                                              let uu___2739_21851 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2739_21851.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____21856 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____21856
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____21900)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21937 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____21937
                                             | uu____21957 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21983 ->
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
                                     let uu___2760_22026 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2760_22026.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____22038 -> failwith "Impossible"  in
                               let uu____22042 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____22042, g, erasable2))))))
           in
        (let uu____22049 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____22049
         then
           let uu____22054 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____22054
         else ());
        (let uu____22059 =
           let uu____22077 =
             let uu___2765_22078 =
               let uu____22079 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____22079 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2765_22078.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2765_22078.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2765_22078.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2765_22078.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2765_22078.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2765_22078.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2765_22078.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2765_22078.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2765_22078.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2765_22078.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2765_22078.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2765_22078.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2765_22078.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2765_22078.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2765_22078.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2765_22078.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2765_22078.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2765_22078.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2765_22078.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2765_22078.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2765_22078.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2765_22078.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2765_22078.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2765_22078.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2765_22078.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2765_22078.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2765_22078.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2765_22078.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2765_22078.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2765_22078.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2765_22078.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2765_22078.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2765_22078.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2765_22078.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2765_22078.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2765_22078.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2765_22078.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2765_22078.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2765_22078.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2765_22078.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2765_22078.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2765_22078.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2765_22078.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2765_22078.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____22095 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____22077 uu____22095 pat_t  in
         match uu____22059 with
         | (bvs,tms,pat_e,pat,g,erasable1) ->
             ((let uu____22134 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22134
               then
                 let uu____22139 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22141 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22139
                   uu____22141
               else ());
              (let uu____22146 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22147 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22146, pat_e, uu____22147, g, erasable1))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.branch ->
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
        let uu____22185 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____22185 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22234 = branch1  in
            (match uu____22234 with
             | (cpat,uu____22265,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22287 =
                   let uu____22294 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22294
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22287 with
                  | (scrutinee_env,uu____22331) ->
                      let uu____22336 = tc_pat env pat_t pattern  in
                      (match uu____22336 with
                       | (pattern1,pat_bvs1,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable1)
                           ->
                           ((let uu____22406 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____22406
                             then
                               let uu____22410 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____22412 =
                                 FStar_Syntax_Print.bvs_to_string ";"
                                   pat_bvs1
                                  in
                               let uu____22415 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____22424 =
                                          let uu____22426 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____22426  in
                                        Prims.op_Hat s uu____22424) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____22410 uu____22412 uu____22415
                             else ());
                            (let uu____22433 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____22463 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____22463
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____22486 =
                                        let uu____22493 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____22493 e  in
                                      match uu____22486 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____22433 with
                             | (when_clause1,g_when) ->
                                 let uu____22550 = tc_term pat_env branch_exp
                                    in
                                 (match uu____22550 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____22609 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun _22620  ->
                                                   FStar_Pervasives_Native.Some
                                                     _22620) uu____22609
                                           in
                                        let branch_guard =
                                          let uu____22624 =
                                            let uu____22626 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____22626  in
                                          if uu____22624
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22682 =
                                                   let uu____22690 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22690
                                                    in
                                                 match uu____22682 with
                                                 | (is_induc,datacons) ->
                                                     if
                                                       (Prims.op_Negation
                                                          is_induc)
                                                         ||
                                                         ((FStar_List.length
                                                             datacons)
                                                            > Prims.int_one)
                                                     then
                                                       let discriminator =
                                                         FStar_Syntax_Util.mk_discriminator
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       let uu____22706 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____22706
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____22727 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____22743
                                                                =
                                                                let uu____22748
                                                                  =
                                                                  let uu____22749
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                  [uu____22749]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc
                                                                  uu____22748
                                                                 in
                                                              uu____22743
                                                                FStar_Pervasives_Native.None
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____22774 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____22774])
                                                     else []
                                                  in
                                               let fail1 uu____22782 =
                                                 let uu____22783 =
                                                   let uu____22785 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____22787 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____22789 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22785 uu____22787
                                                     uu____22789
                                                    in
                                                 failwith uu____22783  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____22804) ->
                                                     head_constructor t1
                                                 | uu____22809 -> fail1 ()
                                                  in
                                               let force_scrutinee
                                                 uu____22815 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____22816 =
                                                       let uu____22818 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____22820 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22818
                                                         uu____22820
                                                        in
                                                     failwith uu____22816
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____22827 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____22827
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22832,FStar_Syntax_Syntax.Tm_name
                                                  uu____22833) -> []
                                               | (uu____22834,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22837 =
                                                     let uu____22838 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____22839 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____22838
                                                       uu____22839 pat_exp2
                                                      in
                                                   [uu____22837]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22840,FStar_Pervasives_Native.Some
                                                   uu____22841)),uu____22842)
                                                   ->
                                                   let uu____22859 =
                                                     let uu____22866 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____22866 with
                                                     | (env1,uu____22880) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____22859 with
                                                    | (uu____22887,t,uu____22889)
                                                        ->
                                                        let uu____22890 =
                                                          let uu____22891 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____22891
                                                            pat_exp2
                                                           in
                                                        [uu____22890])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22892,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22893) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22917 =
                                                     let uu____22919 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22919
                                                      in
                                                   if uu____22917
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22929 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22932 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22929
                                                        uu____22932)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22935,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22936) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22954 =
                                                     let uu____22956 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22956
                                                      in
                                                   if uu____22954
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22966 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22969 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22966
                                                        uu____22969)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22972,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head1,args)) ->
                                                   let f =
                                                     head_constructor head1
                                                      in
                                                   let uu____23019 =
                                                     (let uu____23023 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____23023)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____23019
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____23051 =
                                                          let uu____23056 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23056
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23142
                                                                     ->
                                                                    match uu____23142
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23164),
                                                                    (ei,uu____23166))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23194
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23194
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23215
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23227
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23227
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23229
                                                                    =
                                                                    let uu____23230
                                                                    =
                                                                    let uu____23235
                                                                    =
                                                                    let uu____23236
                                                                    =
                                                                    let uu____23245
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23245
                                                                     in
                                                                    [uu____23236]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23235
                                                                     in
                                                                    uu____23230
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23229
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____23051
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23268 =
                                                        let uu____23271 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23271 f
                                                         in
                                                      FStar_List.append
                                                        uu____23268
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23274,uu____23275) ->
                                                   []
                                               | uu____23282 ->
                                                   let uu____23287 =
                                                     let uu____23289 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23291 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23289
                                                       uu____23291
                                                      in
                                                   failwith uu____23287
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23320 =
                                                 let uu____23322 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23322
                                                  in
                                               if uu____23320
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23328 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23328
                                                     in
                                                  let uu____23337 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23337 with
                                                  | (k,uu____23343) ->
                                                      let uu____23344 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                         in
                                                      (match uu____23344 with
                                                       | (t1,uu____23352,uu____23353)
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
                                        let uu____23367 =
                                          let eqs =
                                            let uu____23389 =
                                              let uu____23391 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____23391
                                               in
                                            if uu____23389
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____23407 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____23422 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____23425 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____23428 ->
                                                   let uu____23429 =
                                                     let uu____23432 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____23432 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____23429)
                                             in
                                          let uu____23435 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____23435 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____23464 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____23464
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____23466 =
                                                let env1 =
                                                  let uu____23472 =
                                                    FStar_All.pipe_right
                                                      pat_bvs1
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____23472
                                                   in
                                                if branch_has_layered_effect
                                                then
                                                  let uu____23480 =
                                                    FStar_TypeChecker_Util.weaken_precondition
                                                      env1 c1
                                                      (FStar_TypeChecker_Common.NonTrivial
                                                         branch_guard)
                                                     in
                                                  (uu____23480,
                                                    FStar_TypeChecker_Env.trivial_guard)
                                                else
                                                  (match (eqs,
                                                           when_condition)
                                                   with
                                                   | uu____23495 when
                                                       let uu____23508 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____23508
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
                                                       let uu____23539 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____23540 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____23539,
                                                         uu____23540)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____23561 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____23561
                                                          in
                                                       let uu____23562 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____23563 =
                                                         let uu____23564 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____23564 g_when
                                                          in
                                                       (uu____23562,
                                                         uu____23563)
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
                                                       let uu____23582 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____23582, g_when))
                                                 in
                                              (match uu____23466 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs1
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return1 =
                                                     let c_weak1 =
                                                       let uu____23625 =
                                                         should_return1 &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____23625
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____23632 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____23632
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
                                                                    let uu____23659
                                                                    =
                                                                    let uu____23668
                                                                    =
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    pat_t  in
                                                                    [uu____23668]
                                                                     in
                                                                    let uu____23687
                                                                    =
                                                                    let uu____23690
                                                                    =
                                                                    let uu____23693
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                    FStar_All.pipe_right
                                                                    uu____23693
                                                                    (fun
                                                                    _23696 
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _23696)
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Total'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                    uu____23690
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____23659
                                                                    uu____23687
                                                                     in
                                                                    let env1
                                                                    =
                                                                    let uu___3006_23698
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    expected_t
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___3006_23698.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }  in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____23701
                                                                    =
                                                                    tc_trivial_guard
                                                                    env1
                                                                    pat_bv_tm
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23701
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])
                                                             [] pat_bv_tms
                                                             pat_bvs1
                                                            in
                                                         let pat_bv_tms2 =
                                                           let uu____23713 =
                                                             FStar_All.pipe_right
                                                               pat_bv_tms1
                                                               (FStar_List.map
                                                                  (fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    let uu____23725
                                                                    =
                                                                    let uu____23730
                                                                    =
                                                                    let uu____23731
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____23731]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____23730
                                                                     in
                                                                    uu____23725
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____23713
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env))
                                                            in
                                                         (let uu____23769 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____23769
                                                          then
                                                            let uu____23774 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____23783
                                                                    =
                                                                    let uu____23785
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23785
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23783)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            FStar_Util.print1
                                                              "tc_eqn: typechecked pat_bv_tms %s"
                                                              uu____23774
                                                          else ());
                                                         FStar_TypeChecker_Util.close_layered_lcomp
                                                           env pat_bvs1
                                                           pat_bv_tms2
                                                           c_weak1))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs1 c_weak1
                                                      in
                                                   ((let uu____23795 =
                                                       (let uu____23799 =
                                                          FStar_TypeChecker_Env.try_lookup_effect_lid
                                                            env
                                                            FStar_Parser_Const.effect_GTot_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____23799)
                                                         &&
                                                         (FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffects"))
                                                        in
                                                     if uu____23795
                                                     then
                                                       let uu____23805 =
                                                         let uu____23807 =
                                                           maybe_return_c_weak
                                                             false
                                                            in
                                                         FStar_TypeChecker_Common.lcomp_to_string
                                                           uu____23807
                                                          in
                                                       FStar_Util.print1
                                                         "tc_eqn: c_weak applied to false: %s\n"
                                                         uu____23805
                                                     else ());
                                                    (let uu____23812 =
                                                       FStar_TypeChecker_Env.close_guard
                                                         env binders
                                                         g_when_weak
                                                        in
                                                     let uu____23813 =
                                                       FStar_TypeChecker_Env.conj_guard
                                                         guard_pat g_branch1
                                                        in
                                                     ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                       (c_weak.FStar_TypeChecker_Common.cflags),
                                                       maybe_return_c_weak,
                                                       uu____23812,
                                                       uu____23813))))
                                           in
                                        match uu____23367 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____23868 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____23868
                                              then
                                                let uu____23871 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____23871
                                              else ());
                                             (let uu____23877 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____23894 =
                                                let uu____23895 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____23895 guard
                                                 in
                                              (uu____23877, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____23894,
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
          let uu____23944 = check_let_bound_def true env1 lb  in
          (match uu____23944 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____23970 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23992 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____23992, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____23998 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____23998
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____23999 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____23999 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____24017 =
                          let uu____24030 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____24030  in
                        (match uu____24017 with
                         | (uu____24080,univs1,e11,c11,gvs) ->
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
                             let uu____24094 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs1, uu____24094)))
                  in
               (match uu____23970 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____24111 =
                      let uu____24120 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24120
                      then
                        let uu____24131 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24131 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24165 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24165
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24166 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24166, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24178 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24178 with
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
                                  let uu____24202 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24202
                                  then e2
                                  else
                                    ((let uu____24210 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24210
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
                    (match uu____24111 with
                     | (e21,c12) ->
                         ((let uu____24234 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24234
                           then
                             let uu____24237 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24237
                           else ());
                          (let e12 =
                             let uu____24243 = FStar_Options.tcnorm ()  in
                             if uu____24243
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
                           (let uu____24249 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24249
                            then
                              let uu____24252 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24252
                            else ());
                           (let cres =
                              let uu____24258 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24258
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
                                   | (wp,uu____24266)::[] -> wp
                                   | uu____24291 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let ret1 =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator
                                      in
                                   let uu____24308 =
                                     let uu____24313 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl ret1
                                        in
                                     let uu____24314 =
                                       let uu____24315 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____24324 =
                                         let uu____24335 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____24335]  in
                                       uu____24315 :: uu____24324  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24313 uu____24314
                                      in
                                   uu____24308 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind1 =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____24372 =
                                     let uu____24377 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl bind1
                                        in
                                     let uu____24378 =
                                       let uu____24379 =
                                         let uu____24388 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____24388
                                          in
                                       let uu____24397 =
                                         let uu____24408 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____24425 =
                                           let uu____24436 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____24445 =
                                             let uu____24456 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____24465 =
                                               let uu____24476 =
                                                 let uu____24485 =
                                                   let uu____24486 =
                                                     let uu____24487 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____24487]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____24486 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____24485
                                                  in
                                               [uu____24476]  in
                                             uu____24456 :: uu____24465  in
                                           uu____24436 :: uu____24445  in
                                         uu____24408 :: uu____24425  in
                                       uu____24379 :: uu____24397  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24377 uu____24378
                                      in
                                   uu____24372 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____24564 =
                                   let uu____24565 =
                                     let uu____24576 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____24576]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____24565;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____24564)
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
                            let uu____24604 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____24618 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____24604, uu____24618,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____24619 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____24630 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____24630
        then
          let universe_of_binders bs =
            let uu____24657 =
              FStar_List.fold_left
                (fun uu____24682  ->
                   fun b  ->
                     match uu____24682 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____24657 with | (uu____24730,us) -> FStar_List.rev us
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
            let uu___3129_24766 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3129_24766.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3129_24766.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3129_24766.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3129_24766.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3129_24766.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3129_24766.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3129_24766.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3129_24766.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3129_24766.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3129_24766.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3129_24766.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3129_24766.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3129_24766.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3129_24766.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3129_24766.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3129_24766.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3129_24766.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3129_24766.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3129_24766.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3129_24766.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3129_24766.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3129_24766.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3129_24766.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3129_24766.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3129_24766.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3129_24766.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3129_24766.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3129_24766.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3129_24766.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3129_24766.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3129_24766.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3129_24766.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3129_24766.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3129_24766.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3129_24766.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3129_24766.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3129_24766.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3129_24766.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3129_24766.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3129_24766.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3129_24766.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3129_24766.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3129_24766.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3129_24766.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____24768 =
            let uu____24780 =
              let uu____24781 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____24781 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____24780 lb  in
          (match uu____24768 with
           | (e1,uu____24804,c1,g1,annotated) ->
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
                  (let uu____24818 =
                     let uu____24824 =
                       let uu____24826 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____24828 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24826 uu____24828
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24824)
                      in
                   FStar_Errors.raise_error uu____24818
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24839 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____24839
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3144_24851 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3144_24851.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3144_24851.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____24852 =
                   let uu____24857 =
                     let uu____24858 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____24858]  in
                   FStar_Syntax_Subst.open_term uu____24857 e2  in
                 match uu____24852 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____24902 = tc_term env_x e21  in
                     (match uu____24902 with
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
                            let uu____24928 =
                              let uu____24935 =
                                let uu____24936 =
                                  let uu____24950 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____24950)  in
                                FStar_Syntax_Syntax.Tm_let uu____24936  in
                              FStar_Syntax_Syntax.mk uu____24935  in
                            uu____24928 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let x_eq_e1 =
                            let uu____24968 =
                              let uu____24969 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_TypeChecker_Common.res_typ
                                 in
                              let uu____24970 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____24969
                                c1.FStar_TypeChecker_Common.res_typ
                                uu____24970 e11
                               in
                            FStar_All.pipe_left
                              (fun _24971  ->
                                 FStar_TypeChecker_Common.NonTrivial _24971)
                              uu____24968
                             in
                          let g21 =
                            let uu____24973 =
                              let uu____24974 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____24974 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____24973
                             in
                          let g22 =
                            let uu____24976 =
                              let uu____24978 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____24978
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24976 xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____24981 =
                            let uu____24983 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____24983  in
                          if uu____24981
                          then
                            let tt =
                              let uu____24994 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____24994
                                FStar_Option.get
                               in
                            ((let uu____25000 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25000
                              then
                                let uu____25005 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25007 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25005 uu____25007
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25014 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25014 with
                             | (t,g_ex) ->
                                 ((let uu____25028 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25028
                                   then
                                     let uu____25033 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25035 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25033 uu____25035
                                   else ());
                                  (let uu____25040 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3177_25042 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3177_25042.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3177_25042.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3177_25042.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25040))))))))
      | uu____25043 ->
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
          let uu____25079 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25079 with
           | (lbs1,e21) ->
               let uu____25098 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25098 with
                | (env0,topt) ->
                    let uu____25117 = build_let_rec_env true env0 lbs1  in
                    (match uu____25117 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25140 = check_let_recs rec_env lbs2  in
                         (match uu____25140 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25160 =
                                  let uu____25161 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25161
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25160
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25167 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25167
                                  (fun _25184  ->
                                     FStar_Pervasives_Native.Some _25184)
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
                                     let uu____25221 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____25255 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____25255)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25221
                                      in
                                   FStar_List.map2
                                     (fun uu____25290  ->
                                        fun lb  ->
                                          match uu____25290 with
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
                                let uu____25338 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____25338
                                 in
                              let uu____25339 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____25339 with
                               | (lbs5,e22) ->
                                   ((let uu____25359 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____25359
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____25360 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____25360, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____25374 -> failwith "Impossible"

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
          let uu____25410 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25410 with
           | (lbs1,e21) ->
               let uu____25429 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25429 with
                | (env0,topt) ->
                    let uu____25448 = build_let_rec_env false env0 lbs1  in
                    (match uu____25448 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25471 =
                           let uu____25478 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____25478
                             (fun uu____25501  ->
                                match uu____25501 with
                                | (lbs3,g) ->
                                    let uu____25520 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____25520))
                            in
                         (match uu____25471 with
                          | (lbs3,g_lbs) ->
                              let uu____25535 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3252_25558 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3252_25558.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3252_25558.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3255_25560 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3255_25560.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____25535 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____25587 = tc_term env2 e21  in
                                   (match uu____25587 with
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
                                          let uu____25611 =
                                            let uu____25612 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____25612 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____25611
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
                                          let uu___3276_25622 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3276_25622.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3276_25622.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3276_25622.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____25630 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____25630))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____25632 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____25632 with
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
                                                  uu____25673 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____25674 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____25674 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3292_25688
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3292_25688.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3292_25688.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3292_25688.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____25689 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____25689))))))))))
      | uu____25690 -> failwith "Impossible"

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
          let uu____25738 = FStar_Options.ml_ish ()  in
          if uu____25738
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____25746 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____25746 with
             | (formals,c) ->
                 let uu____25778 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____25778 with
                  | (actuals,uu____25789,uu____25790) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____25811 =
                          let uu____25817 =
                            let uu____25819 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____25821 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____25819 uu____25821
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____25817)
                           in
                        FStar_Errors.raise_error uu____25811
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____25829 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____25829 actuals
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
                                (let uu____25860 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____25860)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____25879 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____25879)
                               in
                            let msg =
                              let uu____25884 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____25886 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____25884 uu____25886 formals_msg
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
        let uu____25898 =
          FStar_List.fold_left
            (fun uu____25931  ->
               fun lb  ->
                 match uu____25931 with
                 | (lbs1,env1,g_acc) ->
                     let uu____25956 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____25956 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____25979 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____25998 =
                                 let uu____26005 =
                                   let uu____26006 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____26006
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3338_26017 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3338_26017.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3338_26017.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3338_26017.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3338_26017.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3338_26017.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3338_26017.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3338_26017.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3338_26017.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3338_26017.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3338_26017.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3338_26017.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3338_26017.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3338_26017.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3338_26017.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3338_26017.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3338_26017.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3338_26017.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3338_26017.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3338_26017.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3338_26017.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3338_26017.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3338_26017.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3338_26017.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3338_26017.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3338_26017.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3338_26017.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3338_26017.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3338_26017.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3338_26017.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3338_26017.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3338_26017.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3338_26017.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3338_26017.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3338_26017.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3338_26017.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3338_26017.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3338_26017.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3338_26017.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3338_26017.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3338_26017.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3338_26017.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3338_26017.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3338_26017.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3338_26017.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____26005
                                  in
                               match uu____25998 with
                               | (t1,uu____26026,g) ->
                                   let uu____26028 =
                                     let uu____26029 =
                                       let uu____26030 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26030
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26029
                                      in
                                   let uu____26031 = norm env01 t1  in
                                   (uu____26028, uu____26031))
                             in
                          (match uu____25979 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____26051 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____26051
                                 then
                                   let uu___3348_26054 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3348_26054.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3348_26054.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3348_26054.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3348_26054.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3348_26054.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3348_26054.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3348_26054.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3348_26054.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3348_26054.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3348_26054.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3348_26054.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3348_26054.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3348_26054.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3348_26054.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3348_26054.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3348_26054.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3348_26054.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3348_26054.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3348_26054.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3348_26054.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3348_26054.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3348_26054.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3348_26054.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3348_26054.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3348_26054.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3348_26054.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3348_26054.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3348_26054.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3348_26054.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3348_26054.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3348_26054.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3348_26054.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3348_26054.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3348_26054.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3348_26054.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___3348_26054.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3348_26054.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3348_26054.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3348_26054.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3348_26054.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3348_26054.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3348_26054.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3348_26054.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3348_26054.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3351_26068 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3351_26068.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3351_26068.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3351_26068.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3351_26068.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____25898 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26094 =
        let uu____26103 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26129 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26129 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26159 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26159
                       | uu____26166 ->
                           let lb1 =
                             let uu___3368_26169 = lb  in
                             let uu____26170 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26170;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3368_26169.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____26173 =
                             let uu____26180 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____26180
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____26173 with
                            | (e,c,g) ->
                                ((let uu____26189 =
                                    let uu____26191 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____26191  in
                                  if uu____26189
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
        FStar_All.pipe_right uu____26103 FStar_List.unzip  in
      match uu____26094 with
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
        let uu____26247 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____26247 with
        | (env1,uu____26266) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____26274 = check_lbtyp top_level env lb  in
            (match uu____26274 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____26323 =
                     tc_maybe_toplevel_term
                       (let uu___3399_26332 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3399_26332.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3399_26332.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3399_26332.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3399_26332.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3399_26332.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3399_26332.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3399_26332.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3399_26332.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3399_26332.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3399_26332.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3399_26332.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3399_26332.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3399_26332.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3399_26332.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3399_26332.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3399_26332.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3399_26332.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3399_26332.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3399_26332.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3399_26332.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3399_26332.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3399_26332.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3399_26332.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3399_26332.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3399_26332.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3399_26332.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3399_26332.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3399_26332.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3399_26332.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3399_26332.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3399_26332.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3399_26332.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3399_26332.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3399_26332.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3399_26332.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3399_26332.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3399_26332.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3399_26332.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3399_26332.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3399_26332.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3399_26332.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3399_26332.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3399_26332.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3399_26332.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____26323 with
                   | (e12,c1,g1) ->
                       let uu____26347 = (c1, wf_annot)  in
                       (match uu____26347 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____26367 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____26367
                              then
                                let uu____26370 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____26372 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____26374 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____26370 uu____26372 uu____26374
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
            let uu____26413 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26413 with
             | (univ_opening,univ_vars1) ->
                 let uu____26446 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____26446))
        | uu____26451 ->
            let uu____26452 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26452 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____26502 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____26502)
                 else
                   (let uu____26509 = FStar_Syntax_Util.type_u ()  in
                    match uu____26509 with
                    | (k,uu____26529) ->
                        let uu____26530 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____26530 with
                         | (t2,uu____26552,g) ->
                             ((let uu____26555 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____26555
                               then
                                 let uu____26558 =
                                   let uu____26560 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____26560
                                    in
                                 let uu____26561 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____26558 uu____26561
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____26567 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____26567))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____26573  ->
      match uu____26573 with
      | (x,imp) ->
          let uu____26600 = FStar_Syntax_Util.type_u ()  in
          (match uu____26600 with
           | (tu,u) ->
               ((let uu____26622 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____26622
                 then
                   let uu____26625 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____26627 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____26629 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____26625 uu____26627 uu____26629
                 else ());
                (let uu____26634 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____26634 with
                 | (t,uu____26656,g) ->
                     let uu____26658 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____26674 =
                             tc_tactic FStar_Syntax_Syntax.t_unit
                               FStar_Syntax_Syntax.t_unit env tau
                              in
                           (match uu____26674 with
                            | (tau1,uu____26688,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____26692 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____26658 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3460_26727 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3460_26727.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3460_26727.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____26729 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____26729
                            then
                              let uu____26732 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____26736 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26732
                                uu____26736
                            else ());
                           (let uu____26741 = push_binding env x1  in
                            (x1, uu____26741, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____26753 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____26753
       then
         let uu____26756 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____26756
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26869 = tc_binder env1 b  in
             (match uu____26869 with
              | (b1,env',g,u) ->
                  let uu____26918 = aux env' bs2  in
                  (match uu____26918 with
                   | (bs3,env'1,g',us) ->
                       let uu____26979 =
                         let uu____26980 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____26980  in
                       ((b1 :: bs3), env'1, uu____26979, (u :: us))))
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
          (fun uu____27088  ->
             fun uu____27089  ->
               match (uu____27088, uu____27089) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____27181 = tc_term en1 t  in
                     match uu____27181 with
                     | (t1,uu____27201,g') ->
                         let uu____27203 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____27203)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____27257  ->
             match uu____27257 with
             | (pats1,g) ->
                 let uu____27284 = tc_args en p  in
                 (match uu____27284 with
                  | (args,g') ->
                      let uu____27297 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____27297))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____27310 = tc_maybe_toplevel_term env e  in
      match uu____27310 with
      | (e1,c,g) ->
          let uu____27326 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
             in
          if uu____27326
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let uu____27338 = FStar_TypeChecker_Common.lcomp_comp c  in
             match uu____27338 with
             | (c1,g_c) ->
                 let c2 = norm_c env c1  in
                 let uu____27352 =
                   let uu____27358 =
                     FStar_TypeChecker_Util.is_pure_effect env
                       (FStar_Syntax_Util.comp_effect_name c2)
                      in
                   if uu____27358
                   then
                     let uu____27366 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c2)
                        in
                     (uu____27366, false)
                   else
                     (let uu____27371 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Util.comp_result c2)
                         in
                      (uu____27371, true))
                    in
                 (match uu____27352 with
                  | (target_comp,allow_ghost) ->
                      let uu____27384 =
                        FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                      (match uu____27384 with
                       | FStar_Pervasives_Native.Some g' ->
                           let uu____27394 =
                             FStar_TypeChecker_Common.lcomp_of_comp
                               target_comp
                              in
                           let uu____27395 =
                             let uu____27396 =
                               FStar_TypeChecker_Env.conj_guard g_c g'  in
                             FStar_TypeChecker_Env.conj_guard g1 uu____27396
                              in
                           (e1, uu____27394, uu____27395)
                       | uu____27397 ->
                           if allow_ghost
                           then
                             let uu____27407 =
                               FStar_TypeChecker_Err.expected_ghost_expression
                                 e1 c2
                                in
                             FStar_Errors.raise_error uu____27407
                               e1.FStar_Syntax_Syntax.pos
                           else
                             (let uu____27421 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e1 c2
                                 in
                              FStar_Errors.raise_error uu____27421
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
      let uu____27445 = tc_tot_or_gtot_term env t  in
      match uu____27445 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____27476 = tc_check_tot_or_gtot_term env t k  in
        match uu____27476 with
        | (t1,uu____27484,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____27505 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____27505
       then
         let uu____27510 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____27510
       else ());
      (let env1 =
         let uu___3552_27516 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3552_27516.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3552_27516.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3552_27516.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3552_27516.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3552_27516.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3552_27516.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3552_27516.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3552_27516.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3552_27516.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3552_27516.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3552_27516.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3552_27516.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3552_27516.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3552_27516.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3552_27516.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3552_27516.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3552_27516.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3552_27516.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3552_27516.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3552_27516.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3552_27516.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3552_27516.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3552_27516.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3552_27516.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3552_27516.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3552_27516.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3552_27516.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3552_27516.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3552_27516.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3552_27516.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3552_27516.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3552_27516.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3552_27516.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3552_27516.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3552_27516.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3552_27516.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3552_27516.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3552_27516.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3552_27516.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3552_27516.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3552_27516.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3552_27516.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3552_27516.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____27524 =
         try
           (fun uu___3556_27538  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____27559) ->
             let uu____27562 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____27562
          in
       match uu____27524 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____27580 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____27580
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____27591 =
                let uu____27597 =
                  let uu____27599 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____27599
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____27597)
                 in
              let uu____27603 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____27591 uu____27603))
  
let level_of_type_fail :
  'Auu____27619 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____27619
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____27637 =
          let uu____27643 =
            let uu____27645 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____27645 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____27643)  in
        let uu____27649 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____27637 uu____27649
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____27683 =
            let uu____27684 = FStar_Syntax_Util.unrefine t1  in
            uu____27684.FStar_Syntax_Syntax.n  in
          match uu____27683 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____27688 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____27694 = FStar_Syntax_Util.type_u ()  in
                 match uu____27694 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3588_27702 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3588_27702.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3588_27702.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3588_27702.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3588_27702.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3588_27702.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3588_27702.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3588_27702.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3588_27702.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3588_27702.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3588_27702.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3588_27702.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3588_27702.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3588_27702.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3588_27702.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3588_27702.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3588_27702.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3588_27702.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3588_27702.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3588_27702.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3588_27702.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3588_27702.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3588_27702.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3588_27702.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3588_27702.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3588_27702.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3588_27702.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3588_27702.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3588_27702.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3588_27702.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3588_27702.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3588_27702.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3588_27702.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3588_27702.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3588_27702.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3588_27702.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3588_27702.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3588_27702.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3588_27702.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3588_27702.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3588_27702.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3588_27702.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3588_27702.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3588_27702.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3588_27702.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____27707 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____27707
                       | uu____27709 ->
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
      let uu____27726 =
        let uu____27727 = FStar_Syntax_Subst.compress e  in
        uu____27727.FStar_Syntax_Syntax.n  in
      match uu____27726 with
      | FStar_Syntax_Syntax.Tm_bvar uu____27730 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____27733 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____27757 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____27774) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____27819) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27826 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27826 with | ((uu____27835,t),uu____27837) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27843 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____27843
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27846,(FStar_Util.Inl t,uu____27848),uu____27849) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27896,(FStar_Util.Inr c,uu____27898),uu____27899) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27947 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27956;
             FStar_Syntax_Syntax.vars = uu____27957;_},us)
          ->
          let uu____27963 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27963 with
           | ((us',t),uu____27974) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27981 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27981)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____28000 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____28002 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28011) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28038 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28038 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28058  ->
                      match uu____28058 with
                      | (b,uu____28066) ->
                          let uu____28071 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28071) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28076 = universe_of_aux env res  in
                 level_of_type env res uu____28076  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____28187 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____28203 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____28241 ->
                let uu____28242 = universe_of_aux env hd3  in
                (uu____28242, args1)
            | FStar_Syntax_Syntax.Tm_name uu____28253 ->
                let uu____28254 = universe_of_aux env hd3  in
                (uu____28254, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____28265 ->
                let uu____28278 = universe_of_aux env hd3  in
                (uu____28278, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____28289 ->
                let uu____28296 = universe_of_aux env hd3  in
                (uu____28296, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____28307 ->
                let uu____28334 = universe_of_aux env hd3  in
                (uu____28334, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____28345 ->
                let uu____28352 = universe_of_aux env hd3  in
                (uu____28352, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____28363 ->
                let uu____28364 = universe_of_aux env hd3  in
                (uu____28364, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____28375 ->
                let uu____28390 = universe_of_aux env hd3  in
                (uu____28390, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____28401 ->
                let uu____28408 = universe_of_aux env hd3  in
                (uu____28408, args1)
            | FStar_Syntax_Syntax.Tm_type uu____28419 ->
                let uu____28420 = universe_of_aux env hd3  in
                (uu____28420, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____28431,hd4::uu____28433) ->
                let uu____28498 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____28498 with
                 | (uu____28513,uu____28514,hd5) ->
                     let uu____28532 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____28532 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____28589 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____28591 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____28591 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____28649 ->
                let uu____28650 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____28650 with
                 | (env1,uu____28672) ->
                     let env2 =
                       let uu___3749_28678 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3749_28678.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3749_28678.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3749_28678.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3749_28678.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3749_28678.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3749_28678.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3749_28678.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3749_28678.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3749_28678.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3749_28678.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3749_28678.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3749_28678.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3749_28678.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3749_28678.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3749_28678.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3749_28678.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3749_28678.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3749_28678.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3749_28678.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3749_28678.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3749_28678.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3749_28678.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3749_28678.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3749_28678.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3749_28678.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3749_28678.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3749_28678.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3749_28678.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3749_28678.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3749_28678.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3749_28678.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3749_28678.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3749_28678.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3749_28678.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3749_28678.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3749_28678.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3749_28678.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3749_28678.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3749_28678.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3749_28678.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3749_28678.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3749_28678.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____28683 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____28683
                       then
                         let uu____28688 =
                           let uu____28690 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____28690  in
                         let uu____28691 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____28688 uu____28691
                       else ());
                      (let uu____28696 = tc_term env2 hd3  in
                       match uu____28696 with
                       | (uu____28717,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____28718;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____28720;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____28721;_},g)
                           ->
                           ((let uu____28739 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____28739 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____28750 = type_of_head true hd1 args  in
          (match uu____28750 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____28789 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____28789 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____28841 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____28841)))
      | FStar_Syntax_Syntax.Tm_match (uu____28843,hd1::uu____28845) ->
          let uu____28910 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____28910 with
           | (uu____28911,uu____28912,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____28930,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____28977 = universe_of_aux env e  in
      level_of_type env e uu____28977
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____29001 = tc_binders env tps  in
      match uu____29001 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____29059 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29085 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29091 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29091
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29093 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29093
            (fun uu____29107  ->
               match uu____29107 with
               | (t2,uu____29115) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29117;
             FStar_Syntax_Syntax.vars = uu____29118;_},us)
          ->
          let uu____29124 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29124
            (fun uu____29138  ->
               match uu____29138 with
               | (t2,uu____29146) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29147) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29149 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29149
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29151 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29151
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29156;_})
          ->
          let mk_comp =
            let uu____29200 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____29200
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____29231 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____29231
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____29301 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____29301
                 (fun u  ->
                    let uu____29309 =
                      let uu____29312 =
                        let uu____29319 =
                          let uu____29320 =
                            let uu____29335 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____29335)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____29320  in
                        FStar_Syntax_Syntax.mk uu____29319  in
                      uu____29312 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____29309))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____29372 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____29372 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____29431 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____29431
                       (fun uc  ->
                          let uu____29439 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____29439)
                 | (x,imp)::bs3 ->
                     let uu____29465 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____29465
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____29474 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____29494) ->
          let uu____29499 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____29499
            (fun u_x  ->
               let uu____29507 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____29507)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____29512;
             FStar_Syntax_Syntax.vars = uu____29513;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____29592 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29592 with
           | (unary_op1,uu____29612) ->
               let head1 =
                 let uu____29640 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____29640
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
             FStar_Syntax_Syntax.pos = uu____29688;
             FStar_Syntax_Syntax.vars = uu____29689;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____29785 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29785 with
           | (unary_op1,uu____29805) ->
               let head1 =
                 let uu____29833 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____29833
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
             FStar_Syntax_Syntax.pos = uu____29889;
             FStar_Syntax_Syntax.vars = uu____29890;_},uu____29891::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29930;
             FStar_Syntax_Syntax.vars = uu____29931;_},(t2,uu____29933)::uu____29934::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____30030 =
              let uu____30031 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____30031.FStar_Syntax_Syntax.n  in
            match uu____30030 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30104 = FStar_Util.first_N n_args bs  in
                    match uu____30104 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____30192 =
                          let uu____30197 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____30197  in
                        (match uu____30192 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____30251 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____30251 with
                       | (bs1,c1) ->
                           let uu____30272 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____30272
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____30354  ->
                     match uu____30354 with
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
                         let uu____30430 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____30430)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____30432) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____30438,uu____30439) ->
                aux t2
            | uu____30480 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30481,(FStar_Util.Inl t2,uu____30483),uu____30484) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30531,(FStar_Util.Inr c,uu____30533),uu____30534) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____30599 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____30599
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____30607) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____30612 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____30635 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____30649 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____30660 = type_of_well_typed_term env t  in
      match uu____30660 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____30666;
            FStar_Syntax_Syntax.vars = uu____30667;_}
          -> FStar_Pervasives_Native.Some u
      | uu____30670 -> FStar_Pervasives_Native.None

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
            let uu___4028_30698 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4028_30698.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4028_30698.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4028_30698.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4028_30698.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4028_30698.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4028_30698.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4028_30698.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4028_30698.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4028_30698.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4028_30698.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4028_30698.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4028_30698.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4028_30698.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4028_30698.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4028_30698.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4028_30698.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4028_30698.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___4028_30698.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4028_30698.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4028_30698.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4028_30698.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4028_30698.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4028_30698.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4028_30698.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4028_30698.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4028_30698.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4028_30698.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4028_30698.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4028_30698.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4028_30698.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4028_30698.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4028_30698.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4028_30698.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4028_30698.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4028_30698.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4028_30698.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4028_30698.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___4028_30698.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4028_30698.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4028_30698.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4028_30698.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4028_30698.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4028_30698.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4028_30698.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30705 =
            if must_total
            then
              let uu____30707 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30707 with | (uu____30714,uu____30715,g) -> g
            else
              (let uu____30719 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30719 with | (uu____30726,uu____30727,g) -> g)
             in
          let uu____30729 = type_of_well_typed_term env2 t  in
          match uu____30729 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____30734 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____30734
                then
                  let uu____30739 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____30741 = FStar_Syntax_Print.term_to_string t  in
                  let uu____30743 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____30745 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____30739 uu____30741 uu____30743 uu____30745
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____30754 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____30754
                 then
                   let uu____30759 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____30761 = FStar_Syntax_Print.term_to_string t  in
                   let uu____30763 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____30765 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____30759
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____30761 uu____30763 uu____30765
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
            let uu___4059_30802 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4059_30802.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4059_30802.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4059_30802.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4059_30802.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4059_30802.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4059_30802.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4059_30802.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4059_30802.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4059_30802.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4059_30802.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4059_30802.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4059_30802.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4059_30802.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4059_30802.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4059_30802.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4059_30802.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4059_30802.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___4059_30802.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4059_30802.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4059_30802.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4059_30802.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4059_30802.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4059_30802.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4059_30802.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4059_30802.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4059_30802.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4059_30802.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4059_30802.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4059_30802.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4059_30802.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4059_30802.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4059_30802.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4059_30802.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4059_30802.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4059_30802.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4059_30802.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4059_30802.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___4059_30802.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4059_30802.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4059_30802.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4059_30802.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4059_30802.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4059_30802.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4059_30802.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30809 =
            if must_total
            then
              let uu____30811 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30811 with | (uu____30818,uu____30819,g) -> g
            else
              (let uu____30823 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30823 with | (uu____30830,uu____30831,g) -> g)
             in
          let uu____30833 =
            let uu____30835 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____30835  in
          if uu____30833
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  