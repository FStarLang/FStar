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
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___8_5.FStar_TypeChecker_Env.use_eq_strict);
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
      FStar_TypeChecker_Env.mpreprocess =
        (uu___8_5.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
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
      FStar_TypeChecker_Env.use_eq_strict =
        (uu___11_13.FStar_TypeChecker_Env.use_eq_strict);
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
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_13.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_13.FStar_TypeChecker_Env.postprocess);
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
      (fun v  ->
         fun tl  ->
           let r =
             if tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos
                 tl.FStar_Syntax_Syntax.pos
              in
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v  in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl  in [uu____75]
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
  
let steps : 'uuuuuu130 . 'uuuuuu130 -> FStar_TypeChecker_Env.step Prims.list
  =
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
                       (let fail uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head
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
                             | uu____333 -> fail ())))
             in
          aux false kt
  
let push_binding :
  'uuuuuu344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu344) -> FStar_TypeChecker_Env.env
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
      fun v  ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v)) ::
          s
  
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
                   FStar_TypeChecker_Util.check_has_type env e lc t'  in
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
                            "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
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
                                  (fun uu____622  ->
                                     FStar_Pervasives_Native.Some uu____622)
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
  'uuuuuu1071 'uuuuuu1072 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1071 * 'uuuuuu1072 * FStar_TypeChecker_Env.guard_t) ->
        ('uuuuuu1071 * 'uuuuuu1072 * FStar_TypeChecker_Env.guard_t)
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
        | (head,args) ->
            let uu____1211 =
              let uu____1226 =
                let uu____1227 = FStar_Syntax_Util.un_uinst head  in
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
                    (FStar_Syntax_Syntax.Implicit uu____1271))::(hd,FStar_Pervasives_Native.None
                                                                 )::(tl,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd  in
                 let tlvs = get_pat_vars' all andlist tl  in
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
  'uuuuuu1477 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'uuuuuu1477) Prims.list -> unit
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
        | (head,args) ->
            let uu____1647 =
              let uu____1662 =
                let uu____1663 = FStar_Syntax_Util.un_uinst head  in
                uu____1663.FStar_Syntax_Syntax.n  in
              (uu____1662, args)  in
            (match uu____1647 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1679) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1701::(hd,uu____1703)::(tl,uu____1705)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1772 = pat_terms hd  in
                 let uu____1775 = pat_terms tl  in
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
        | FStar_Syntax_Syntax.Tm_quoted uu____2008 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____2016 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____2016 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2049 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2066  ->
                   match uu____2066 with
                   | (t3,uu____2078) ->
                       let uu____2083 = aux t3  in
                       FStar_List.append acc uu____2083) uu____2049 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2087,uu____2088) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2130) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2136) -> aux t2  in
      let tlist =
        let uu____2144 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2144 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2167 =
                    let uu____2169 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2169  in
                  Prims.op_Hat s uu____2167) "" tlist
            in
         let uu____2173 =
           let uu____2179 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2179)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2173)
  
let check_smt_pat :
  'uuuuuu2194 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2194) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2235 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2235
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2238;
                  FStar_Syntax_Syntax.effect_name = uu____2239;
                  FStar_Syntax_Syntax.result_typ = uu____2240;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2244)::[];
                  FStar_Syntax_Syntax.flags = uu____2245;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2307 -> failwith "Impossible"
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
              let uu___373_2370 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___373_2370.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___373_2370.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___373_2370.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___373_2370.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___373_2370.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___373_2370.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___373_2370.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___373_2370.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___373_2370.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___373_2370.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___373_2370.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___373_2370.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___373_2370.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___373_2370.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___373_2370.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___373_2370.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.use_eq_strict =
                  (uu___373_2370.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (uu___373_2370.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___373_2370.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___373_2370.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___373_2370.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___373_2370.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___373_2370.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___373_2370.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___373_2370.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___373_2370.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___373_2370.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___373_2370.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___373_2370.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___373_2370.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___373_2370.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___373_2370.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___373_2370.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___373_2370.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___373_2370.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___373_2370.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___373_2370.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___373_2370.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___373_2370.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___373_2370.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___373_2370.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___373_2370.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___373_2370.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___373_2370.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___373_2370.FStar_TypeChecker_Env.erasable_types_tab)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2396 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2396
               then
                 let uu____2399 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2402 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2399 uu____2402
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2436  ->
                         match uu____2436 with
                         | (b,uu____2446) ->
                             let t =
                               let uu____2452 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2452
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2455 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2456 -> []
                              | uu____2471 ->
                                  let uu____2472 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2472])))
                  in
               let as_lex_list dec =
                 let uu____2485 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2485 with
                 | (head,uu____2505) ->
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2533 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2541 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2550  ->
                         match uu___1_2550 with
                         | FStar_Syntax_Syntax.DECREASES uu____2552 -> true
                         | uu____2556 -> false))
                  in
               match uu____2541 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2563 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2584 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2613 =
              match uu____2613 with
              | (l,t,u_names) ->
                  let uu____2637 =
                    let uu____2638 = FStar_Syntax_Subst.compress t  in
                    uu____2638.FStar_Syntax_Syntax.n  in
                  (match uu____2637 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2697  ->
                                 match uu____2697 with
                                 | (x,imp) ->
                                     let uu____2716 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2716
                                     then
                                       let uu____2725 =
                                         let uu____2726 =
                                           let uu____2729 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2729
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2726
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2725, imp)
                                     else (x, imp)))
                          in
                       let uu____2736 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2736 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2757 =
                                let uu____2762 =
                                  let uu____2763 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2772 =
                                    let uu____2783 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2783]  in
                                  uu____2763 :: uu____2772  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2762
                                 in
                              uu____2757 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2818 = FStar_Util.prefix formals2  in
                            (match uu____2818 with
                             | (bs,(last,imp)) ->
                                 let last1 =
                                   let uu___440_2881 = last  in
                                   let uu____2882 =
                                     FStar_Syntax_Util.refine last precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___440_2881.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___440_2881.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2882
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last1, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2918 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Medium
                                      in
                                   if uu____2918
                                   then
                                     let uu____2921 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2923 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2925 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2921 uu____2923 uu____2925
                                   else ());
                                  (l, t', u_names))))
                   | uu____2932 ->
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
               let uu____2996 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2996)
  
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____3019 =
      let uu____3020 = FStar_Syntax_Subst.compress e  in
      uu____3020.FStar_Syntax_Syntax.n  in
    match uu____3019 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1,(FStar_Util.Inr uu____3032,uu____3033),uu____3034) ->
        let uu____3081 =
          let uu____3082 = FStar_Syntax_Subst.compress e1  in
          uu____3082.FStar_Syntax_Syntax.n  in
        (match uu____3081 with
         | FStar_Syntax_Syntax.Tm_app (head,args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____3129 =
               let uu____3130 = FStar_Syntax_Subst.compress head  in
               uu____3130.FStar_Syntax_Syntax.n  in
             (match uu____3129 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____3142 =
                    let uu____3149 = FStar_All.pipe_right args FStar_List.hd
                       in
                    FStar_All.pipe_right uu____3149
                      (fun uu____3205  ->
                         match uu____3205 with | (e2,aqual) -> (l, e2, aqual))
                     in
                  FStar_All.pipe_right uu____3142
                    (fun uu____3258  ->
                       FStar_Pervasives_Native.Some uu____3258)
              | uu____3259 -> FStar_Pervasives_Native.None)
         | uu____3266 -> FStar_Pervasives_Native.None)
    | uu____3273 -> FStar_Pervasives_Native.None
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3934 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3934
       then
         let uu____3937 =
           let uu____3939 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3939  in
         let uu____3941 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____3943 = FStar_Syntax_Print.term_to_string e  in
         let uu____3945 =
           let uu____3947 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3947  in
         let uu____3948 =
           let uu____3950 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____3950 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3937 uu____3941 uu____3943 uu____3945 uu____3948
       else ());
      (let uu____3959 =
         FStar_Util.record_time
           (fun uu____3978  ->
              tc_maybe_toplevel_term
                (let uu___484_3981 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___484_3981.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___484_3981.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___484_3981.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___484_3981.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___484_3981.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___484_3981.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___484_3981.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___484_3981.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___484_3981.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___484_3981.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___484_3981.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___484_3981.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___484_3981.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___484_3981.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___484_3981.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___484_3981.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___484_3981.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___484_3981.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___484_3981.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___484_3981.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___484_3981.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___484_3981.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___484_3981.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___484_3981.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___484_3981.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___484_3981.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___484_3981.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___484_3981.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___484_3981.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___484_3981.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___484_3981.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___484_3981.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___484_3981.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___484_3981.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___484_3981.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___484_3981.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___484_3981.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___484_3981.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___484_3981.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___484_3981.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___484_3981.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___484_3981.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___484_3981.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___484_3981.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___484_3981.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____3959 with
       | (r,ms) ->
           ((let uu____4006 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____4006
             then
               ((let uu____4010 =
                   let uu____4012 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____4012
                    in
                 let uu____4014 = FStar_Syntax_Print.term_to_string e  in
                 let uu____4016 =
                   let uu____4018 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____4018  in
                 let uu____4019 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____4010 uu____4014 uu____4016 uu____4019);
                (let uu____4022 = r  in
                 match uu____4022 with
                 | (e1,lc,uu____4031) ->
                     let uu____4032 =
                       let uu____4034 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4034
                        in
                     let uu____4036 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4038 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4040 =
                       let uu____4042 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4042  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4032 uu____4036 uu____4038 uu____4040))
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
      (let uu____4060 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4060
       then
         let uu____4063 =
           let uu____4065 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4065  in
         let uu____4067 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4069 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4063 uu____4067
           uu____4069
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4080 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4102 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4109 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4122 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4123 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4124 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4125 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4126 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4145 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4160 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4167 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4183 =
             match uu___2_4183 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4189 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4205 =
                 let uu____4206 = FStar_Syntax_Subst.compress t  in
                 uu____4206.FStar_Syntax_Syntax.n  in
               match uu____4205 with
               | FStar_Syntax_Syntax.Tm_name uu____4210 -> true
               | uu____4212 -> false  in
             FStar_Util.for_some
               (fun uu____4222  ->
                  match uu____4222 with
                  | (uu____4228,t) ->
                      let uu____4230 = is_name t  in
                      Prims.op_Negation uu____4230)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4249  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4292  ->
                       match uu____4292 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___557_4321 = qi  in
                  let uu____4322 =
                    FStar_List.map
                      (fun uu____4350  ->
                         match uu____4350 with
                         | ((bv,uu____4366),bv') ->
                             let uu____4378 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4378)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___557_4321.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4322
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
                         let uu____4390 =
                           let uu____4397 =
                             let uu____4398 =
                               let uu____4412 =
                                 let uu____4415 =
                                   let uu____4416 =
                                     let uu____4423 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4423
                                      in
                                   [uu____4416]  in
                                 FStar_Syntax_Subst.close uu____4415 t  in
                               ((false, [lb]), uu____4412)  in
                             FStar_Syntax_Syntax.Tm_let uu____4398  in
                           FStar_Syntax_Syntax.mk uu____4397  in
                         uu____4390 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4459 =
                  FStar_List.fold_right
                    (fun uu____4495  ->
                       fun uu____4496  ->
                         match (uu____4495, uu____4496) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4565 = tc_term env_tm tm  in
                             (match uu____4565 with
                              | (tm1,uu____4583,g) ->
                                  let uu____4585 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4585))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4459 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___585_4627 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___585_4627.FStar_Syntax_Syntax.qkind);
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
                let uu____4638 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4638 with
                 | (env',uu____4652) ->
                     let uu____4657 =
                       tc_term
                         (let uu___594_4666 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___594_4666.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___594_4666.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___594_4666.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___594_4666.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___594_4666.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___594_4666.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___594_4666.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___594_4666.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___594_4666.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___594_4666.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___594_4666.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___594_4666.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___594_4666.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___594_4666.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___594_4666.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___594_4666.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___594_4666.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___594_4666.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___594_4666.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___594_4666.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___594_4666.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___594_4666.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___594_4666.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___594_4666.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___594_4666.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___594_4666.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___594_4666.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___594_4666.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___594_4666.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___594_4666.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___594_4666.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___594_4666.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___594_4666.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___594_4666.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___594_4666.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___594_4666.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___594_4666.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___594_4666.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___594_4666.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___594_4666.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___594_4666.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___594_4666.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___594_4666.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___594_4666.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___594_4666.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4657 with
                      | (qt1,uu____4675,uu____4676) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4682 =
                            let uu____4689 =
                              let uu____4694 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4694  in
                            value_check_expected_typ env1 top uu____4689
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4682 with
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
           { FStar_Syntax_Syntax.blob = uu____4711;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4712;
             FStar_Syntax_Syntax.ltyp = uu____4713;
             FStar_Syntax_Syntax.rng = uu____4714;_}
           ->
           let uu____4725 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4725
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4732 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4732 with
            | (e2,c,g) ->
                let g1 =
                  let uu___624_4749 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___624_4749.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___624_4749.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___624_4749.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4750 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4750, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names,pats)) ->
           let uu____4792 = FStar_Syntax_Util.type_u ()  in
           (match uu____4792 with
            | (t,u) ->
                let uu____4805 = tc_check_tot_or_gtot_term env1 e1 t ""  in
                (match uu____4805 with
                 | (e2,c,g) ->
                     let uu____4822 =
                       let uu____4839 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4839 with
                       | (env2,uu____4863) -> tc_smt_pats env2 pats  in
                     (match uu____4822 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___647_4901 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___647_4901.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___647_4901.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___647_4901.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4902 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4921 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4902, c, uu____4921))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4927 =
             let uu____4928 = FStar_Syntax_Subst.compress e1  in
             uu____4928.FStar_Syntax_Syntax.n  in
           (match uu____4927 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4937,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4939;
                               FStar_Syntax_Syntax.lbtyp = uu____4940;
                               FStar_Syntax_Syntax.lbeff = uu____4941;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4943;
                               FStar_Syntax_Syntax.lbpos = uu____4944;_}::[]),e2)
                ->
                let uu____4975 =
                  let uu____4982 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4982 e11  in
                (match uu____4975 with
                 | (e12,c1,g1) ->
                     let uu____4992 = tc_term env1 e2  in
                     (match uu____4992 with
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
                            let uu____5016 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____5016
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5026 =
                              let uu____5033 =
                                let uu____5034 =
                                  let uu____5048 =
                                    let uu____5056 =
                                      let uu____5059 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____5059]  in
                                    (false, uu____5056)  in
                                  (uu____5048, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____5034  in
                              FStar_Syntax_Syntax.mk uu____5033  in
                            uu____5026 FStar_Pervasives_Native.None
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
                          let uu____5083 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5083)))
            | uu____5084 ->
                let uu____5085 = tc_term env1 e1  in
                (match uu____5085 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5107) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5119) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5138 = tc_term env1 e1  in
           (match uu____5138 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5159,(FStar_Util.Inr expected_c,_tacopt),uu____5162) when
           let uu____5209 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5209 FStar_Util.is_some ->
           let uu____5241 =
             let uu____5252 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5252 FStar_Util.must  in
           (match uu____5241 with
            | (effect_lid,e1,aqual) ->
                let uu____5326 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5326 with
                 | (env0,uu____5340) ->
                     let uu____5345 = tc_comp env0 expected_c  in
                     (match uu____5345 with
                      | (expected_c1,uu____5359,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5363 =
                              let uu____5365 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5365  in
                            if uu____5363
                            then
                              let uu____5368 =
                                let uu____5374 =
                                  let uu____5376 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5378 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5376 uu____5378
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5374)
                                 in
                              FStar_Errors.raise_error uu____5368
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5385 =
                              let uu____5387 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5387  in
                            if uu____5385
                            then
                              let uu____5390 =
                                let uu____5396 =
                                  let uu____5398 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5398
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5396)
                                 in
                              FStar_Errors.raise_error uu____5390
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5408 =
                                let uu____5411 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5411 u_c
                                 in
                              FStar_All.pipe_right uu____5408 FStar_Util.must
                               in
                            let e2 =
                              let uu____5417 =
                                let uu____5424 =
                                  let uu____5425 =
                                    let uu____5452 =
                                      let uu____5469 =
                                        let uu____5478 =
                                          FStar_Syntax_Syntax.mk_Total' repr
                                            (FStar_Pervasives_Native.Some u_c)
                                           in
                                        FStar_Util.Inr uu____5478  in
                                      (uu____5469,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (e1, uu____5452,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____5425
                                   in
                                FStar_Syntax_Syntax.mk uu____5424  in
                              uu____5417 FStar_Pervasives_Native.None
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5520 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5520
                             then
                               let uu____5524 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5524
                             else ());
                            (let uu____5529 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5529 with
                             | (e3,uu____5543,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5547 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5547
                                   then
                                     let uu____5551 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5553 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5551 uu____5553
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
                                     let uu____5600 =
                                       let uu____5607 =
                                         let uu____5608 =
                                           let uu____5635 =
                                             let uu____5638 =
                                               FStar_All.pipe_right
                                                 expected_c1
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5638
                                               (fun uu____5643  ->
                                                  FStar_Pervasives_Native.Some
                                                    uu____5643)
                                              in
                                           (tm1,
                                             ((FStar_Util.Inr expected_c1),
                                               _tacopt), uu____5635)
                                            in
                                         FStar_Syntax_Syntax.Tm_ascribed
                                           uu____5608
                                          in
                                       FStar_Syntax_Syntax.mk uu____5607  in
                                     uu____5600 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let uu____5680 =
                                     let uu____5687 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5687
                                      in
                                   match uu____5680 with
                                   | (top2,c,g_env) ->
                                       let uu____5697 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5697)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5701) ->
           let uu____5748 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5748 with
            | (env0,uu____5762) ->
                let uu____5767 = tc_comp env0 expected_c  in
                (match uu____5767 with
                 | (expected_c1,uu____5781,g) ->
                     let uu____5783 =
                       let uu____5790 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5790 e1  in
                     (match uu____5783 with
                      | (e2,c',g') ->
                          let uu____5800 =
                            let uu____5811 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5811 with
                            | (c'1,g_c') ->
                                let uu____5828 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5828 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____5848 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____5848))
                             in
                          (match uu____5800 with
                           | (e3,expected_c2,g'') ->
                               let uu____5870 = tc_tactic_opt env0 topt  in
                               (match uu____5870 with
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
                                      let uu____5930 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5930
                                       in
                                    let uu____5931 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5931 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5948 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5948
                                            in
                                         let uu____5949 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5949)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5953) ->
           let uu____6000 = FStar_Syntax_Util.type_u ()  in
           (match uu____6000 with
            | (k,u) ->
                let uu____6013 = tc_check_tot_or_gtot_term env1 t k ""  in
                (match uu____6013 with
                 | (t1,uu____6028,f) ->
                     let uu____6030 = tc_tactic_opt env1 topt  in
                     (match uu____6030 with
                      | (topt1,gtac) ->
                          let uu____6049 =
                            let uu____6056 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6056 e1  in
                          (match uu____6049 with
                           | (e2,c,g) ->
                               let uu____6066 =
                                 let uu____6071 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____6077  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____6071 e2 c f
                                  in
                               (match uu____6066 with
                                | (c1,f1) ->
                                    let uu____6087 =
                                      let uu____6094 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____6094
                                        c1
                                       in
                                    (match uu____6087 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____6141 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____6141
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____6143 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____6143)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6144;
              FStar_Syntax_Syntax.vars = uu____6145;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6224 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6224 with
            | (unary_op,uu____6248) ->
                let head =
                  let uu____6276 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6276
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6324;
              FStar_Syntax_Syntax.vars = uu____6325;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6404 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6404 with
            | (unary_op,uu____6428) ->
                let head =
                  let uu____6456 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6456
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6504);
              FStar_Syntax_Syntax.pos = uu____6505;
              FStar_Syntax_Syntax.vars = uu____6506;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6585 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6585 with
            | (unary_op,uu____6609) ->
                let head =
                  let uu____6637 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6637
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6685;
              FStar_Syntax_Syntax.vars = uu____6686;_},a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6782 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6782 with
            | (unary_op,uu____6806) ->
                let head =
                  let uu____6834 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____6834
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6890;
              FStar_Syntax_Syntax.vars = uu____6891;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6929 =
             let uu____6936 =
               let uu____6937 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6937  in
             tc_term uu____6936 e1  in
           (match uu____6929 with
            | (e2,c,g) ->
                let uu____6961 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6961 with
                 | (head,uu____6985) ->
                     let uu____7010 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7043 =
                       let uu____7044 =
                         let uu____7045 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7045  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7044
                        in
                     (uu____7010, uu____7043, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7046;
              FStar_Syntax_Syntax.vars = uu____7047;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7100 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7100 with
            | (head,uu____7124) ->
                let env' =
                  let uu____7150 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7150  in
                let uu____7151 = tc_term env' r  in
                (match uu____7151 with
                 | (er,uu____7165,gr) ->
                     let uu____7167 = tc_term env1 t  in
                     (match uu____7167 with
                      | (t1,tt,gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt  in
                          let uu____7184 =
                            let uu____7185 =
                              let uu____7190 =
                                let uu____7191 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____7200 =
                                  let uu____7211 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____7211]  in
                                uu____7191 :: uu____7200  in
                              FStar_Syntax_Syntax.mk_Tm_app head uu____7190
                               in
                            uu____7185 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7184, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7244;
              FStar_Syntax_Syntax.vars = uu____7245;_},uu____7246)
           ->
           let uu____7271 =
             let uu____7277 =
               let uu____7279 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7279  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7277)  in
           FStar_Errors.raise_error uu____7271 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7289;
              FStar_Syntax_Syntax.vars = uu____7290;_},uu____7291)
           ->
           let uu____7316 =
             let uu____7322 =
               let uu____7324 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7324  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7322)  in
           FStar_Errors.raise_error uu____7316 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7334;
              FStar_Syntax_Syntax.vars = uu____7335;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7382 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7382 with
             | (env0,uu____7396) ->
                 let uu____7401 = tc_term env0 e1  in
                 (match uu____7401 with
                  | (e2,c,g) ->
                      let uu____7417 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7417 with
                       | (reify_op,uu____7441) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7467 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7467 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7482 =
                                    let uu____7484 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7484  in
                                  if uu____7482
                                  then
                                    let uu____7487 =
                                      let uu____7493 =
                                        let uu____7495 =
                                          FStar_Ident.string_of_lid ef  in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7495
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7493)
                                       in
                                    FStar_Errors.raise_error uu____7487
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
                                    let uu____7538 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7541 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7541
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7538
                                    then
                                      let uu____7544 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7544
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
                                       let uu____7556 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7556
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7557 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7557 with
                                  | (e4,c3,g') ->
                                      let uu____7573 =
                                        let uu____7574 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7574
                                         in
                                      (e4, c3, uu____7573))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7576;
              FStar_Syntax_Syntax.vars = uu____7577;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7625 =
               let uu____7627 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7627  in
             if uu____7625
             then
               let uu____7630 =
                 let uu____7636 =
                   let uu____7638 = FStar_Ident.string_of_lid l  in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7638
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7636)  in
               FStar_Errors.raise_error uu____7630 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7644 = FStar_Syntax_Util.head_and_args top  in
             match uu____7644 with
             | (reflect_op,uu____7668) ->
                 let uu____7693 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7693 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7714 =
                        let uu____7720 =
                          let uu____7722 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7722
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7720)  in
                      FStar_Errors.raise_error uu____7714
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7744 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7744 with
                       | (env_no_ex,uu____7758) ->
                           let uu____7763 =
                             let uu____7772 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7772 with
                             | (e2,c,g) ->
                                 ((let uu____7791 =
                                     let uu____7793 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7793
                                      in
                                   if uu____7791
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7763 with
                            | (e2,c_e,g_e) ->
                                let uu____7831 =
                                  let uu____7846 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____7846 with
                                  | (a,u_a) ->
                                      let uu____7867 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____7867 with
                                       | (a_uvar,uu____7896,g_a) ->
                                           let uu____7910 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____7910, u_a, a_uvar, g_a))
                                   in
                                (match uu____7831 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____7952 =
                                         let uu____7953 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____7953.FStar_Syntax_Syntax.n  in
                                       match uu____7952 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7966,uu____7967::args) ->
                                           args
                                       | uu____8009 ->
                                           let uu____8010 =
                                             let uu____8016 =
                                               let uu____8018 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____8020 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____8022 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____8018 uu____8020
                                                 uu____8022
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____8016)
                                              in
                                           FStar_Errors.raise_error
                                             uu____8010
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8037 =
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
                                       FStar_All.pipe_right uu____8037
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8073 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8073 with
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
                                          let uu____8096 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8096))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8135 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8135 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,(uu____8185,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____8186))::(tau,FStar_Pervasives_Native.None
                                                               )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8239 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8239 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8314 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8524 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8314 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8643 =
               let uu____8644 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8644 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8643 instantiate_both  in
           ((let uu____8660 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8660
             then
               let uu____8663 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8665 = FStar_Syntax_Print.term_to_string top  in
               let uu____8667 =
                 let uu____8669 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8669
                   (fun uu___3_8676  ->
                      match uu___3_8676 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8663
                 uu____8665 uu____8667
             else ());
            (let uu____8685 = tc_term (no_inst env2) head  in
             match uu____8685 with
             | (head1,chead,g_head) ->
                 let uu____8701 =
                   let uu____8706 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8706
                     (fun uu____8723  ->
                        match uu____8723 with
                        | (c,g) ->
                            let uu____8734 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8734))
                    in
                 (match uu____8701 with
                  | (chead1,g_head1) ->
                      let uu____8743 =
                        let uu____8750 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8753 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8753))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1)
                           in
                        if uu____8750
                        then
                          let uu____8762 =
                            let uu____8769 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8769
                             in
                          match uu____8762 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8783 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8783)
                         in
                      (match uu____8743 with
                       | (e1,c,g) ->
                           let uu____8795 =
                             let uu____8802 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8802
                             then
                               let uu____8811 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8811 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8827 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8827, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8795 with
                            | (e2,c1,implicits) ->
                                ((let uu____8840 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8840
                                  then
                                    let uu____8843 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8843
                                  else ());
                                 (let uu____8848 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8848 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8867 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8867
                                        then
                                          let uu____8870 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8872 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8870 uu____8872
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8877 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8900;
                FStar_Syntax_Syntax.lbunivs = uu____8901;
                FStar_Syntax_Syntax.lbtyp = uu____8902;
                FStar_Syntax_Syntax.lbeff = uu____8903;
                FStar_Syntax_Syntax.lbdef = uu____8904;
                FStar_Syntax_Syntax.lbattrs = uu____8905;
                FStar_Syntax_Syntax.lbpos = uu____8906;_}::[]),uu____8907)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____8933),uu____8934) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8952;
                FStar_Syntax_Syntax.lbunivs = uu____8953;
                FStar_Syntax_Syntax.lbtyp = uu____8954;
                FStar_Syntax_Syntax.lbeff = uu____8955;
                FStar_Syntax_Syntax.lbdef = uu____8956;
                FStar_Syntax_Syntax.lbattrs = uu____8957;
                FStar_Syntax_Syntax.lbpos = uu____8958;_}::uu____8959),uu____8960)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____8988),uu____8989) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____9015 =
        let uu____9016 = FStar_Syntax_Subst.compress top  in
        uu____9016.FStar_Syntax_Syntax.n  in
      match uu____9015 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9063 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9063 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9083 = tc_term env11 e1  in
               (match uu____9083 with
                | (e11,c1,g1) ->
                    let uu____9099 =
                      let uu____9110 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9110 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9099 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9165 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9179 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9179 with
                                | (k,uu____9191) ->
                                    let uu____9192 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9192 with
                                     | (res_t,uu____9213,g) ->
                                         let uu____9227 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9228 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9227, res_t, uu____9228)))
                            in
                         (match uu____9165 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9239 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9239
                                then
                                  let uu____9242 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9242
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
                                let uu____9350 =
                                  let uu____9358 =
                                    FStar_List.fold_right
                                      (fun uu____9451  ->
                                         fun uu____9452  ->
                                           match (uu____9451, uu____9452)
                                           with
                                           | ((branch,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable)) ->
                                               let uu____9724 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9724,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9358 with
                                  | (cases,g,erasable) ->
                                      let uu____9838 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x
                                         in
                                      (uu____9838, g, erasable)
                                   in
                                match uu____9350 with
                                | (c_branches,g_branches,erasable) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches)
                                       in
                                    let cres1 =
                                      if erasable
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool  in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero)
                                           in
                                        let uu____9858 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9858
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____10000  ->
                                                  match uu____10000 with
                                                  | ((pat,wopt,br),uu____10048,eff_label,uu____10050,uu____10051,uu____10052,uu____10053)
                                                      ->
                                                      let uu____10092 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10092)))
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
                                      let uu____10159 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10159
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10167 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10167  in
                                         let lb =
                                           let uu____10171 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10171 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10177 =
                                             let uu____10184 =
                                               let uu____10185 =
                                                 let uu____10199 =
                                                   let uu____10202 =
                                                     let uu____10203 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         guard_x
                                                        in
                                                     [uu____10203]  in
                                                   FStar_Syntax_Subst.close
                                                     uu____10202 e_match
                                                    in
                                                 ((false, [lb]), uu____10199)
                                                  in
                                               FStar_Syntax_Syntax.Tm_let
                                                 uu____10185
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10184
                                              in
                                           uu____10177
                                             FStar_Pervasives_Native.None
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10236 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10236
                                      then
                                        let uu____10239 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10241 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10239 uu____10241
                                      else ());
                                     (let uu____10246 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10246)))))))))
      | uu____10247 ->
          let uu____10248 =
            let uu____10250 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10250  in
          failwith uu____10248

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
  fun head  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____10275 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10314))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10355 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10275 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10388 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10388 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10392 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10392)
                 in
              let uu____10395 =
                let uu____10402 =
                  let uu____10403 =
                    let uu____10404 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10404
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10403  in
                tc_term uu____10402 typ  in
              (match uu____10395 with
               | (typ1,uu____10420,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10423 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10423 with
                     | (tau1,uu____10437,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1324_10442 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1324_10442.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1324_10442.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10444 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10444
                            then
                              let uu____10449 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10449
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10455 =
                              let uu____10456 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10456
                               in
                            (t, uu____10455,
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
            let uu___1334_10462 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1334_10462.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1334_10462.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1334_10462.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1334_10462.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1334_10462.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1334_10462.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1334_10462.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1334_10462.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1334_10462.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1334_10462.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1334_10462.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1334_10462.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1334_10462.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1334_10462.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1334_10462.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1334_10462.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1334_10462.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1334_10462.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1334_10462.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1334_10462.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1334_10462.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1334_10462.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1334_10462.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1334_10462.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1334_10462.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1334_10462.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1334_10462.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1334_10462.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1334_10462.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1334_10462.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1334_10462.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1334_10462.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1334_10462.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1334_10462.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1334_10462.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1334_10462.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1334_10462.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1334_10462.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1334_10462.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1334_10462.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1334_10462.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1334_10462.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1334_10462.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1334_10462.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1334_10462.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____10464 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10464 ""

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
          let uu____10487 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10487 with
           | (tactic1,uu____10501,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v dc e1 t0 =
        let t = FStar_Syntax_Util.remove_inacc t0  in
        let uu____10554 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____10554 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____10575 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10575
              then FStar_Util.Inl t1
              else
                (let uu____10584 =
                   let uu____10585 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10585
                    in
                 FStar_Util.Inr uu____10584)
               in
            let is_data_ctor uu___4_10594 =
              match uu___4_10594 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10599) -> true
              | uu____10607 -> false  in
            let uu____10611 =
              (is_data_ctor dc) &&
                (let uu____10614 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10614)
               in
            if uu____10611
            then
              let uu____10623 =
                let uu____10629 =
                  let uu____10631 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v  in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10631
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10629)  in
              let uu____10635 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10623 uu____10635
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10653 =
            let uu____10659 =
              let uu____10661 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10661
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10659)  in
          FStar_Errors.raise_error uu____10653 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10689 =
            let uu____10694 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10694  in
          value_check_expected_typ env1 e uu____10689
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10696 =
            let uu____10709 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10709 with
            | FStar_Pervasives_Native.None  ->
                let uu____10724 = FStar_Syntax_Util.type_u ()  in
                (match uu____10724 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10696 with
           | (t,uu____10762,g0) ->
               let uu____10776 =
                 let uu____10789 =
                   let uu____10791 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____10791
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____10789 r env1 t
                  in
               (match uu____10776 with
                | (e1,uu____10801,g1) ->
                    let uu____10815 =
                      let uu____10816 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10816
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10817 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10815, uu____10817)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10819 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10829 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____10829)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10819 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1400_10843 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1400_10843.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1400_10843.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____10846 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____10846 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____10867 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____10867
                       then FStar_Util.Inl t1
                       else
                         (let uu____10876 =
                            let uu____10877 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10877
                             in
                          FStar_Util.Inr uu____10876)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10879;
             FStar_Syntax_Syntax.vars = uu____10880;_},uu____10881)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10886 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10886
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10896 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10896
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10906;
             FStar_Syntax_Syntax.vars = uu____10907;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____10916 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10916 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10940 =
                     let uu____10946 =
                       let uu____10948 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____10950 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____10952 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10948 uu____10950 uu____10952
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10946)
                      in
                   let uu____10956 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____10940 uu____10956)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10973 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10978 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10978 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10979,us) ->
          let uu____10985 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10985
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10995 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10995 with
           | ((us,t),range) ->
               ((let uu____11018 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____11018
                 then
                   let uu____11023 =
                     let uu____11025 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____11025  in
                   let uu____11026 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____11028 = FStar_Range.string_of_range range  in
                   let uu____11030 = FStar_Range.string_of_use_range range
                      in
                   let uu____11032 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____11023 uu____11026 uu____11028 uu____11030
                     uu____11032
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____11040 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____11040 us  in
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
          let uu____11068 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____11068 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____11082 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11082 with
                | (env2,uu____11096) ->
                    let uu____11101 = tc_binders env2 bs1  in
                    (match uu____11101 with
                     | (bs2,env3,g,us) ->
                         let uu____11120 = tc_comp env3 c1  in
                         (match uu____11120 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1484_11139 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1484_11139.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1484_11139.FStar_Syntax_Syntax.vars)
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
                                  let uu____11150 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____11150
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
          let uu____11167 =
            let uu____11172 =
              let uu____11173 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11173]  in
            FStar_Syntax_Subst.open_term uu____11172 phi  in
          (match uu____11167 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____11201 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11201 with
                | (env2,uu____11215) ->
                    let uu____11220 =
                      let uu____11235 = FStar_List.hd x1  in
                      tc_binder env2 uu____11235  in
                    (match uu____11220 with
                     | (x2,env3,f1,u) ->
                         ((let uu____11271 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____11271
                           then
                             let uu____11274 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____11276 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11278 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____11274 uu____11276 uu____11278
                           else ());
                          (let uu____11285 = FStar_Syntax_Util.type_u ()  in
                           match uu____11285 with
                           | (t_phi,uu____11297) ->
                               let uu____11298 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                   "refinement formula must be pure or ghost"
                                  in
                               (match uu____11298 with
                                | (phi2,uu____11313,f2) ->
                                    let e1 =
                                      let uu___1522_11318 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1522_11318.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1522_11318.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____11327 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____11327
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11356) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____11383 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____11383
            then
              let uu____11386 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1535_11390 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1535_11390.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1535_11390.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11386
            else ());
           (let uu____11406 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____11406 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____11419 ->
          let uu____11420 =
            let uu____11422 = FStar_Syntax_Print.term_to_string top  in
            let uu____11424 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11422
              uu____11424
             in
          failwith uu____11420

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____11436 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____11438,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____11451,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____11469 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____11475 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____11477 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____11478 ->
            let uu____11480 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____11480 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____11485 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____11486 =
              let uu____11492 =
                let uu____11494 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11494
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11492)  in
            FStar_Errors.raise_error uu____11486 r
        | FStar_Const.Const_set_range_of  ->
            let uu____11498 =
              let uu____11504 =
                let uu____11506 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11506
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11504)  in
            FStar_Errors.raise_error uu____11498 r
        | FStar_Const.Const_reify  ->
            let uu____11510 =
              let uu____11516 =
                let uu____11518 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11518
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11516)  in
            FStar_Errors.raise_error uu____11510 r
        | FStar_Const.Const_reflect uu____11522 ->
            let uu____11523 =
              let uu____11529 =
                let uu____11531 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11531
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11529)  in
            FStar_Errors.raise_error uu____11523 r
        | uu____11535 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____11554) ->
          let uu____11563 = FStar_Syntax_Util.type_u ()  in
          (match uu____11563 with
           | (k,u) ->
               let uu____11576 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11576 with
                | (t1,uu____11591,g) ->
                    let uu____11593 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11593, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____11595) ->
          let uu____11604 = FStar_Syntax_Util.type_u ()  in
          (match uu____11604 with
           | (k,u) ->
               let uu____11617 = tc_check_tot_or_gtot_term env t k ""  in
               (match uu____11617 with
                | (t1,uu____11632,g) ->
                    let uu____11634 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11634, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let head1 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____11644 =
              let uu____11649 =
                let uu____11650 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____11650 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head1 uu____11649  in
            uu____11644 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11667 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff ""  in
          (match uu____11667 with
           | (tc1,uu____11682,f) ->
               let uu____11684 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11684 with
                | (head2,args) ->
                    let comp_univs =
                      let uu____11734 =
                        let uu____11735 = FStar_Syntax_Subst.compress head2
                           in
                        uu____11735.FStar_Syntax_Syntax.n  in
                      match uu____11734 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11738,us) -> us
                      | uu____11744 -> []  in
                    let uu____11745 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____11745 with
                     | (uu____11768,args1) ->
                         let uu____11794 =
                           let uu____11817 = FStar_List.hd args1  in
                           let uu____11834 = FStar_List.tl args1  in
                           (uu____11817, uu____11834)  in
                         (match uu____11794 with
                          | (res,args2) ->
                              let uu____11915 =
                                let uu____11924 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11952  ->
                                          match uu___5_11952 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11960 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____11960 with
                                               | (env1,uu____11972) ->
                                                   let uu____11977 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____11977 with
                                                    | (e1,uu____11989,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____11924
                                  FStar_List.unzip
                                 in
                              (match uu____11915 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1664_12030 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1664_12030.FStar_Syntax_Syntax.effect_name);
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
                                   let uu____12036 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____12036))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____12046 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____12050 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____12060 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____12060
        | FStar_Syntax_Syntax.U_max us ->
            let uu____12064 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____12064
        | FStar_Syntax_Syntax.U_name x ->
            let uu____12068 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____12068
            then u2
            else
              (let uu____12073 =
                 let uu____12075 =
                   let uu____12077 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____12077 " not found"  in
                 Prims.op_Hat "Universe variable " uu____12075  in
               failwith uu____12073)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____12084 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____12084 FStar_Pervasives_Native.snd
         | uu____12093 -> aux u)

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
          let fail msg t =
            let uu____12124 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____12124 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____12213 bs2 bs_expected1 =
              match uu____12213 with
              | (env2,subst) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst)
                   | ((uu____12320,FStar_Pervasives_Native.None )::uu____12321,
                      (hd_e,q)::uu____12324) when
                       FStar_Syntax_Syntax.is_implicit_or_meta q ->
                       let bv =
                         let uu____12376 =
                           let uu____12379 =
                             FStar_Ident.range_of_id
                               hd_e.FStar_Syntax_Syntax.ppname
                              in
                           FStar_Pervasives_Native.Some uu____12379  in
                         let uu____12380 =
                           FStar_Syntax_Subst.subst subst
                             hd_e.FStar_Syntax_Syntax.sort
                            in
                         FStar_Syntax_Syntax.new_bv uu____12376 uu____12380
                          in
                       aux (env2, subst) ((bv, q) :: bs2) bs_expected1
                   | ((hd,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta
                              uu____12475),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12476)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____12491),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12492)) -> true
                           | uu____12501 -> false  in
                         let uu____12511 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____12514 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____12514 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____12511
                         then
                           let uu____12516 =
                             let uu____12522 =
                               let uu____12524 =
                                 FStar_Syntax_Print.bv_to_string hd  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____12524
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____12522)
                              in
                           let uu____12528 =
                             FStar_Syntax_Syntax.range_of_bv hd  in
                           FStar_Errors.raise_error uu____12516 uu____12528
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____12532 =
                           let uu____12539 =
                             let uu____12540 =
                               FStar_Syntax_Util.unmeta
                                 hd.FStar_Syntax_Syntax.sort
                                in
                             uu____12540.FStar_Syntax_Syntax.n  in
                           match uu____12539 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12551 ->
                               ((let uu____12553 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____12553
                                 then
                                   let uu____12556 =
                                     FStar_Syntax_Print.bv_to_string hd  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____12556
                                 else ());
                                (let uu____12561 =
                                   tc_tot_or_gtot_term env2
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____12561 with
                                 | (t,uu____12575,g1_env) ->
                                     let g2_env =
                                       let uu____12578 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       match uu____12578 with
                                       | FStar_Pervasives_Native.Some g ->
                                           FStar_All.pipe_right g
                                             (FStar_TypeChecker_Rel.resolve_implicits
                                                env2)
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____12582 =
                                             FStar_TypeChecker_Rel.get_subtyping_prop
                                               env2 expected_t t
                                              in
                                           (match uu____12582 with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____12585 =
                                                  FStar_TypeChecker_Err.basic_type_error
                                                    env2
                                                    FStar_Pervasives_Native.None
                                                    expected_t t
                                                   in
                                                let uu____12591 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____12585 uu____12591
                                            | FStar_Pervasives_Native.Some
                                                g_env ->
                                                FStar_TypeChecker_Util.label_guard
                                                  (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                  "Type annotation on parameter incompatible with the expected type"
                                                  g_env)
                                        in
                                     let uu____12594 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____12594)))
                            in
                         match uu____12532 with
                         | (t,g_env) ->
                             let hd1 =
                               let uu___1776_12620 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1776_12620.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1776_12620.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd1, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst1 =
                               let uu____12643 =
                                 FStar_Syntax_Syntax.bv_to_name hd1  in
                               maybe_extend_subst subst b_expected
                                 uu____12643
                                in
                             let uu____12646 =
                               aux (env_b, subst1) bs3 bs_expected2  in
                             (match uu____12646 with
                              | (env_bs,bs4,rest,g'_env_b,subst2) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____12711 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____12711,
                                    subst2))))
                   | (rest,[]) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst)
                   | ([],rest) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst))
               in
            aux (env1, []) bs1 bs_expected  in
          let rec expected_function_typ env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____12883 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____12893 = tc_binders env1 bs  in
                  match uu____12893 with
                  | (bs1,envbody,g_env,uu____12923) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____12969 =
                    let uu____12970 = FStar_Syntax_Subst.compress t2  in
                    uu____12970.FStar_Syntax_Syntax.n  in
                  match uu____12969 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____12993 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____13013 -> failwith "Impossible");
                       (let uu____13023 = tc_binders env1 bs  in
                        match uu____13023 with
                        | (bs1,envbody,g_env,uu____13055) ->
                            let uu____13056 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13056 with
                             | (envbody1,uu____13084) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____13095;
                         FStar_Syntax_Syntax.pos = uu____13096;
                         FStar_Syntax_Syntax.vars = uu____13097;_},uu____13098)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____13142 -> failwith "Impossible");
                       (let uu____13152 = tc_binders env1 bs  in
                        match uu____13152 with
                        | (bs1,envbody,g_env,uu____13184) ->
                            let uu____13185 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13185 with
                             | (envbody1,uu____13213) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____13225) ->
                      let uu____13230 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____13230 with
                       | (uu____13271,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____13318 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____13318 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____13453 c_expected2
                               body3 =
                               match uu____13453 with
                               | (env_bs,bs2,more,guard_env,subst) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____13567 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____13567,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____13584 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____13584
                                           in
                                        let uu____13585 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env_bs, bs2, guard_env, uu____13585,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected2
                                           in
                                        let uu____13602 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____13602
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
                                               let uu____13668 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____13668 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____13695 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____13695 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst1)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____13750 =
                                                           let uu____13777 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____13777,
                                                             subst1)
                                                            in
                                                         handle_more
                                                           uu____13750
                                                           c_expected4 body3))
                                           | uu____13800 ->
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
                             let uu____13829 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____13829 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1902_13894 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1902_13894.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1902_13894.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1902_13894.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1902_13894.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1902_13894.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1902_13894.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1902_13894.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1902_13894.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1902_13894.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1902_13894.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1902_13894.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1902_13894.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1902_13894.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1902_13894.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1902_13894.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1902_13894.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___1902_13894.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1902_13894.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1902_13894.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1902_13894.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1902_13894.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1902_13894.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1902_13894.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1902_13894.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1902_13894.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1902_13894.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1902_13894.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1902_13894.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1902_13894.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1902_13894.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1902_13894.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1902_13894.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1902_13894.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1902_13894.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1902_13894.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___1902_13894.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1902_13894.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___1902_13894.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1902_13894.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1902_13894.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1902_13894.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1902_13894.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1902_13894.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1902_13894.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___1902_13894.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             let uu____13901 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____13967  ->
                                       fun uu____13968  ->
                                         match (uu____13967, uu____13968)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____14059 =
                                               let uu____14066 =
                                                 let uu____14067 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____14067
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____14066 t3  in
                                             (match uu____14059 with
                                              | (t4,uu____14091,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____14104 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1920_14107
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1920_14107.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1920_14107.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____14104 ::
                                                          letrec_binders
                                                    | uu____14108 ->
                                                        letrec_binders
                                                     in
                                                  let uu____14113 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____14113)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____13901 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____14133 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____14133)
                              in
                           let uu____14136 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____14136 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____14172 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____14172 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____14209 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____14209))))
                  | uu____14216 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____14238 =
                          let uu____14239 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____14239
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____14238
                      else
                        (let uu____14243 =
                           expected_function_typ env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____14243 with
                         | (uu____14282,bs1,uu____14284,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14306 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14306 with
          | (env1,topt) ->
              ((let uu____14326 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14326
                then
                  let uu____14329 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14329
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14343 = expected_function_typ env1 topt body  in
                match uu____14343 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14384 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14384
                      then
                        let uu____14387 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14392 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14397 =
                          let uu____14399 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14399 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14387 uu____14392 uu____14397
                      else ());
                     (let uu____14409 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14409
                      then
                        let uu____14414 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14417 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14414 uu____14417
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14423 =
                        let should_check_expected_effect =
                          let uu____14436 =
                            let uu____14443 =
                              let uu____14444 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____14444.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____14443)  in
                          match uu____14436 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____14450,(FStar_Util.Inr
                                           expected_c,uu____14452),uu____14453))
                              -> false
                          | uu____14503 -> true  in
                        let uu____14511 =
                          tc_term
                            (let uu___1993_14520 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1993_14520.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1993_14520.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1993_14520.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1993_14520.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1993_14520.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1993_14520.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1993_14520.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1993_14520.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1993_14520.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1993_14520.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1993_14520.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1993_14520.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1993_14520.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1993_14520.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1993_14520.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1993_14520.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1993_14520.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1993_14520.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1993_14520.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1993_14520.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1993_14520.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1993_14520.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1993_14520.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1993_14520.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1993_14520.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1993_14520.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1993_14520.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1993_14520.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1993_14520.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1993_14520.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1993_14520.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1993_14520.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1993_14520.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1993_14520.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1993_14520.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1993_14520.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1993_14520.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1993_14520.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1993_14520.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1993_14520.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1993_14520.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1993_14520.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1993_14520.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1993_14520.FStar_TypeChecker_Env.erasable_types_tab)
                             }) body1
                           in
                        match uu____14511 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____14547 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____14547 with
                               | (cbody1,g_lc) ->
                                   let uu____14564 =
                                     check_expected_effect
                                       (let uu___2004_14573 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___2004_14573.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___2004_14573.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___2004_14573.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___2004_14573.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___2004_14573.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___2004_14573.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___2004_14573.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___2004_14573.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___2004_14573.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___2004_14573.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___2004_14573.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___2004_14573.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___2004_14573.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___2004_14573.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___2004_14573.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___2004_14573.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___2004_14573.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___2004_14573.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___2004_14573.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___2004_14573.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___2004_14573.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___2004_14573.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___2004_14573.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___2004_14573.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___2004_14573.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___2004_14573.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___2004_14573.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___2004_14573.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___2004_14573.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___2004_14573.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___2004_14573.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___2004_14573.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____14564 with
                                    | (body3,cbody2,guard) ->
                                        let uu____14587 =
                                          let uu____14588 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____14588
                                           in
                                        (body3, cbody2, uu____14587)))
                            else
                              (let uu____14595 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____14595 with
                               | (cbody1,g_lc) ->
                                   let uu____14612 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____14612))
                         in
                      match uu____14423 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14635 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14638 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14638)
                               in
                            if uu____14635
                            then
                              let uu____14641 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14642 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14641
                                uu____14642
                            else
                              (let guard =
                                 let uu____14646 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14646
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
                          let uu____14661 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14685
                                     -> (e, t_annot, guard1)
                                 | uu____14700 ->
                                     let lc =
                                       let uu____14702 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____14702
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____14703 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1
                                        in
                                     (match uu____14703 with
                                      | (e1,uu____14717,guard') ->
                                          let uu____14719 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____14719)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____14661 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____14730 =
                                 let uu____14735 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14735 guard2
                                  in
                               (match uu____14730 with
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
    fun head  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = FStar_Syntax_Util.comp_result chead  in
              (let uu____14786 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____14786
               then
                 let uu____14789 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let uu____14791 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14789
                   uu____14791
               else ());
              (let monadic_application uu____14873 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14873 with
                 | (head1,chead1,ghead1,cres) ->
                     let uu____14942 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____14942 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____14956 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14972 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14972
                                   in
                                (cres1, g)
                            | uu____14973 ->
                                let g =
                                  let uu____14983 =
                                    let uu____14984 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____14984
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14983
                                   in
                                let uu____14985 =
                                  let uu____14986 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____14986
                                   in
                                (uu____14985, g)
                             in
                          (match uu____14956 with
                           | (cres2,guard1) ->
                               ((let uu____14996 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____14996
                                 then
                                   let uu____14999 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14999
                                 else ());
                                (let uu____15004 =
                                   let uu____15009 =
                                     let uu____15010 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____15010
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____15011 =
                                     let uu____15012 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____15012
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____15009, uu____15011)  in
                                 match uu____15004 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15036  ->
                                                 match uu____15036 with
                                                 | (uu____15046,uu____15047,lc)
                                                     ->
                                                     (let uu____15055 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15055)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev)
                                          in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head1
                                           (FStar_List.rev arg_rets_rev)
                                           FStar_Pervasives_Native.None
                                           head1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15068 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15068
                                       then
                                         ((let uu____15072 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15072
                                           then
                                             let uu____15075 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15075
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15083 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15083
                                           then
                                             let uu____15086 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15086
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15117  ->
                                              match uu____15117 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15159 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15159
                                                    then
                                                      let uu____15162 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15167 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15169 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15162
                                                        uu____15167
                                                        uu____15169
                                                    else ());
                                                   (let uu____15174 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15174
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
                                       (let uu____15185 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15185
                                        then
                                          let uu____15188 =
                                            FStar_Syntax_Print.term_to_string
                                              head1
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15188
                                        else ());
                                       (let uu____15193 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15193
                                        then
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some
                                               head1) chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)
                                        else
                                          FStar_TypeChecker_Util.bind
                                            head1.FStar_Syntax_Syntax.pos env
                                            FStar_Pervasives_Native.None
                                            chead2
                                            (FStar_Pervasives_Native.None,
                                              comp))
                                        in
                                     let shortcuts_evaluation_order =
                                       let uu____15204 =
                                         let uu____15205 =
                                           FStar_Syntax_Subst.compress head1
                                            in
                                         uu____15205.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15204 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15210 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15233  ->
                                                  match uu____15233 with
                                                  | (arg,uu____15247,uu____15248)
                                                      -> arg :: args1) []
                                             arg_comps_rev
                                            in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head1 args1
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
                                         (let uu____15259 =
                                            let map_fun uu____15325 =
                                              match uu____15325 with
                                              | ((e,q),uu____15366,c) ->
                                                  ((let uu____15389 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15389
                                                    then
                                                      let uu____15392 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15394 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15392
                                                        uu____15394
                                                    else ());
                                                   (let uu____15399 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15399
                                                    then
                                                      ((let uu____15425 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15425
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
                                                           (let uu____15466 =
                                                              let uu____15468
                                                                =
                                                                let uu____15469
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1
                                                                   in
                                                                uu____15469.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15468
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15474
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15474
                                                              | uu____15476
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15466)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15480 =
                                                            let uu____15486 =
                                                              let uu____15488
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15490
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name
                                                                 in
                                                              let uu____15492
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15488
                                                                uu____15490
                                                                uu____15492
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15486)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15480)
                                                       else ();
                                                       (let uu____15499 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15499
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
                                                        let uu____15507 =
                                                          let uu____15516 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15516, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15507)))))
                                               in
                                            let uu____15545 =
                                              let uu____15576 =
                                                let uu____15605 =
                                                  let uu____15616 =
                                                    let uu____15625 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1
                                                       in
                                                    (uu____15625,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15616 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15605
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15576
                                               in
                                            match uu____15545 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____15826 =
                                                  let uu____15827 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15827
                                                   in
                                                let uu____15848 =
                                                  let uu____15849 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____15849
                                                   in
                                                (lifted_args, uu____15826,
                                                  uu____15848)
                                             in
                                          match uu____15259 with
                                          | (lifted_args,head2,args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head2 args1
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
                                                uu___6_15960 =
                                                match uu___6_15960 with
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
                                                      let uu____16021 =
                                                        let uu____16028 =
                                                          let uu____16029 =
                                                            let uu____16043 =
                                                              let uu____16046
                                                                =
                                                                let uu____16047
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____16047]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____16046 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____16043)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____16029
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____16028
                                                         in
                                                      uu____16021
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
                                     let uu____16099 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____16099 with
                                      | (comp2,g) ->
                                          ((let uu____16117 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16117
                                            then
                                              let uu____16120 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16122 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16120 uu____16122
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16203 bs args1 =
                 match uu____16203 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16342))::rest,
                         (uu____16344,FStar_Pervasives_Native.None )::uu____16345)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16406 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t
                             in
                          (match uu____16406 with
                           | (t1,g_ex) ->
                               let uu____16419 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____16419 with
                                | (varg,uu____16440,implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst  in
                                    let arg =
                                      let uu____16468 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16468)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16477 =
                                      let uu____16512 =
                                        let uu____16523 =
                                          let uu____16532 =
                                            let uu____16533 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____16533
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16532)
                                           in
                                        uu____16523 :: outargs  in
                                      (subst1, uu____16512, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16477 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____16579,FStar_Pervasives_Native.None
                                                                 )::uu____16580)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst tau  in
                          let uu____16642 =
                            tc_tactic FStar_Syntax_Syntax.t_unit
                              FStar_Syntax_Syntax.t_unit env tau1
                             in
                          (match uu____16642 with
                           | (tau2,uu____16656,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16659 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t
                                  in
                               (match uu____16659 with
                                | (t1,g_ex) ->
                                    let uu____16672 =
                                      let uu____16685 =
                                        let uu____16692 =
                                          let uu____16697 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____16697, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____16692
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____16685
                                       in
                                    (match uu____16672 with
                                     | (varg,uu____16710,implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst  in
                                         let arg =
                                           let uu____16738 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____16738)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____16747 =
                                           let uu____16782 =
                                             let uu____16793 =
                                               let uu____16802 =
                                                 let uu____16803 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____16803
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16802)
                                                in
                                             uu____16793 :: outargs  in
                                           (subst1, uu____16782, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____16747 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16919,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16920)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____16931),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16932)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____16940),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16941)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____16956 ->
                                let uu____16965 =
                                  let uu____16971 =
                                    let uu____16973 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____16975 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____16977 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____16979 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16973 uu____16975 uu____16977
                                      uu____16979
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16971)
                                   in
                                FStar_Errors.raise_error uu____16965
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual  in
                            let x1 =
                              let uu___2283_16986 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2283_16986.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2283_16986.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____16988 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____16988
                             then
                               let uu____16991 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____16993 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16995 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16997 =
                                 FStar_Syntax_Print.subst_to_string subst  in
                               let uu____16999 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16991 uu____16993 uu____16995
                                 uu____16997 uu____16999
                             else ());
                            (let uu____17004 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ
                                in
                             match uu____17004 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2292_17019 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2292_17019.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2292_17019.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2292_17019.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2292_17019.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2292_17019.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2292_17019.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2292_17019.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2292_17019.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2292_17019.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2292_17019.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2292_17019.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2292_17019.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2292_17019.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2292_17019.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2292_17019.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2292_17019.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2292_17019.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2292_17019.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2292_17019.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2292_17019.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2292_17019.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2292_17019.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2292_17019.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2292_17019.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2292_17019.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2292_17019.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2292_17019.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2292_17019.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2292_17019.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2292_17019.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2292_17019.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2292_17019.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2292_17019.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2292_17019.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2292_17019.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2292_17019.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2292_17019.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2292_17019.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2292_17019.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2292_17019.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2292_17019.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2292_17019.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2292_17019.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2292_17019.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2292_17019.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____17021 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____17021
                                   then
                                     let uu____17024 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____17026 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____17028 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     let uu____17030 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq
                                        in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____17024 uu____17026 uu____17028
                                       uu____17030
                                   else ());
                                  (let uu____17035 = tc_term env2 e  in
                                   match uu____17035 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17052 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17052
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17075 =
                                           let uu____17078 =
                                             let uu____17087 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17087
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17078
                                            in
                                         (uu____17075, aq)  in
                                       let uu____17096 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17096
                                       then
                                         let subst1 =
                                           let uu____17106 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst
                                             uu____17106 e1
                                            in
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____17205,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17241) ->
                          let uu____17292 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____17292 with
                           | (head1,chead1,ghead1) ->
                               let uu____17314 =
                                 let uu____17319 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____17319
                                   (fun uu____17336  ->
                                      match uu____17336 with
                                      | (c,g1) ->
                                          let uu____17347 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____17347))
                                  in
                               (match uu____17314 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17390 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____17390
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____17421 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____17421 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____17444 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____17444
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
                                      | uu____17491 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17499 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____17499
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____17500 =
                                              let uu____17501 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____17501.FStar_Syntax_Syntax.n
                                               in
                                            match uu____17500 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17504;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17505;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____17507)
                                                -> norm_tres tres4
                                            | uu____17515 -> tres3  in
                                          let uu____17516 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____17516
                                      | uu____17518 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____17521 ->
                                          let uu____17522 =
                                            let uu____17528 =
                                              let uu____17530 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____17532 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____17534 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17530 uu____17532
                                                uu____17534
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17528)
                                             in
                                          let uu____17538 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____17522 uu____17538
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____17568 =
                   let uu____17569 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____17569.FStar_Syntax_Syntax.n  in
                 match uu____17568 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17578 ->
                     let uu____17591 =
                       FStar_List.fold_right
                         (fun uu____17622  ->
                            fun uu____17623  ->
                              match uu____17623 with
                              | (bs,guard1) ->
                                  let uu____17650 =
                                    let uu____17663 =
                                      let uu____17664 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17664
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17663
                                     in
                                  (match uu____17650 with
                                   | (t,uu____17681,g) ->
                                       let uu____17695 =
                                         let uu____17698 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17698 :: bs  in
                                       let uu____17699 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17695, uu____17699))) args
                         ([], guard)
                        in
                     (match uu____17591 with
                      | (bs,guard1) ->
                          let uu____17716 =
                            let uu____17723 =
                              let uu____17736 =
                                let uu____17737 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17737
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17736
                               in
                            match uu____17723 with
                            | (t,uu____17754,g) ->
                                let uu____17768 = FStar_Options.ml_ish ()  in
                                if uu____17768
                                then
                                  let uu____17777 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17780 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17777, uu____17780)
                                else
                                  (let uu____17785 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17788 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17785, uu____17788))
                             in
                          (match uu____17716 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17807 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17807
                                 then
                                   let uu____17811 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____17813 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17815 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17811 uu____17813 uu____17815
                                 else ());
                                (let g =
                                   let uu____17821 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17821
                                    in
                                 let uu____17822 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17822))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17823;
                        FStar_Syntax_Syntax.pos = uu____17824;
                        FStar_Syntax_Syntax.vars = uu____17825;_},uu____17826)
                     ->
                     let uu____17863 =
                       FStar_List.fold_right
                         (fun uu____17894  ->
                            fun uu____17895  ->
                              match uu____17895 with
                              | (bs,guard1) ->
                                  let uu____17922 =
                                    let uu____17935 =
                                      let uu____17936 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17936
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17935
                                     in
                                  (match uu____17922 with
                                   | (t,uu____17953,g) ->
                                       let uu____17967 =
                                         let uu____17970 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17970 :: bs  in
                                       let uu____17971 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17967, uu____17971))) args
                         ([], guard)
                        in
                     (match uu____17863 with
                      | (bs,guard1) ->
                          let uu____17988 =
                            let uu____17995 =
                              let uu____18008 =
                                let uu____18009 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18009
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18008
                               in
                            match uu____17995 with
                            | (t,uu____18026,g) ->
                                let uu____18040 = FStar_Options.ml_ish ()  in
                                if uu____18040
                                then
                                  let uu____18049 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18052 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18049, uu____18052)
                                else
                                  (let uu____18057 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18060 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18057, uu____18060))
                             in
                          (match uu____17988 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18079 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18079
                                 then
                                   let uu____18083 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18085 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18087 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18083 uu____18085 uu____18087
                                 else ());
                                (let g =
                                   let uu____18093 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18093
                                    in
                                 let uu____18094 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18094))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18117 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18117 with
                      | (bs1,c1) ->
                          let head_info = (head, chead, ghead, c1)  in
                          ((let uu____18140 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18140
                            then
                              let uu____18143 =
                                FStar_Syntax_Print.term_to_string head  in
                              let uu____18145 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18147 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18150 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18143 uu____18145 uu____18147
                                uu____18150
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18196) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18202,uu____18203) ->
                     check_function_app t guard
                 | uu____18244 ->
                     let uu____18245 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18245
                       head.FStar_Syntax_Syntax.pos
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
    fun head  ->
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
                  let uu____18328 =
                    FStar_List.fold_left2
                      (fun uu____18397  ->
                         fun uu____18398  ->
                           fun uu____18399  ->
                             match (uu____18397, uu____18398, uu____18399)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____18552 =
                                     let uu____18554 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____18554 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____18552
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18560 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                       "arguments to short circuiting operators must be pure or ghost"
                                      in
                                   match uu____18560 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g1 =
                                         let uu____18590 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18590 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18595 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____18595)
                                              &&
                                              (let uu____18598 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____18598))
                                          in
                                       let uu____18600 =
                                         let uu____18611 =
                                           let uu____18622 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____18622]  in
                                         FStar_List.append seen uu____18611
                                          in
                                       let uu____18655 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____18600, uu____18655, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____18328 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____18723 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____18723
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____18726 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____18726 with | (c2,g) -> (e, c2, g)))
              | uu____18743 ->
                  check_application_args env head chead g_head args
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
        let fail msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p
           in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t  in
            let uu____18841 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18841 with
            | (head,args) ->
                let uu____18884 =
                  let uu____18885 = FStar_Syntax_Subst.compress head  in
                  uu____18885.FStar_Syntax_Syntax.n  in
                (match uu____18884 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18889;
                        FStar_Syntax_Syntax.vars = uu____18890;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18897 ->
                     if norm1
                     then t1
                     else
                       (let uu____18901 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____18901))
          
          and unfold_once t f us args =
            let uu____18919 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____18919
            then t
            else
              (let uu____18924 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____18924 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18944 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____18944 with
                    | (uu____18949,head_def) ->
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
          let uu____18956 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____18956  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18975 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____18975
           then
             let uu____18980 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____18982 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18980 uu____18982
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____19002 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____19004 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____19002 uu____19004 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____19008 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____19008 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19052 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19052 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19053;
                    FStar_Syntax_Syntax.pos = uu____19054;
                    FStar_Syntax_Syntax.vars = uu____19055;_} ->
                    let uu____19058 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19058 with
                     | (head_p,args_p) ->
                         let uu____19101 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19101
                         then
                           let uu____19104 =
                             let uu____19105 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19105.FStar_Syntax_Syntax.n  in
                           (match uu____19104 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19110 =
                                    let uu____19112 =
                                      let uu____19114 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19114
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19112
                                     in
                                  if uu____19110
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____19142 =
                                    let uu____19167 =
                                      let uu____19171 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19171
                                       in
                                    match uu____19167 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____19220 =
                                          FStar_Util.first_N n args_p  in
                                        (match uu____19220 with
                                         | (params_p,uu____19278) ->
                                             let uu____19319 =
                                               FStar_Util.first_N n args_s
                                                in
                                             (match uu____19319 with
                                              | (params_s,uu____19377) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19142 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____19506  ->
                                             fun uu____19507  ->
                                               match (uu____19506,
                                                       uu____19507)
                                               with
                                               | ((p,uu____19541),(s,uu____19543))
                                                   ->
                                                   let uu____19576 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____19576 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____19579 =
                                                          let uu____19581 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____19583 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19581
                                                            uu____19583
                                                           in
                                                        fail1 uu____19579
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
                            | uu____19588 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19592 =
                              let uu____19594 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____19596 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19594 uu____19596
                               in
                            fail1 uu____19592))
                | uu____19599 ->
                    let uu____19600 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____19600 with
                     | FStar_Pervasives_Native.None  -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____19643 = FStar_Syntax_Util.head_and_args e  in
          match uu____19643 with
          | (head,args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19713 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____19713 with
                    | (us,t_f) ->
                        let uu____19733 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____19733 with
                         | (formals,t) ->
                             let erasable =
                               FStar_TypeChecker_Env.non_informative env1 t
                                in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____19846 formals1 args1 =
                                 match uu____19846 with
                                 | (subst,args_out,bvs,guard) ->
                                     (match (formals1, args1) with
                                      | ([],[]) ->
                                          let head1 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head us
                                             in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head1 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____19997 =
                                            FStar_Syntax_Subst.subst subst t
                                             in
                                          (pat_e, uu____19997, bvs, guard,
                                            erasable)
                                      | ((f1,uu____20004)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____20062 =
                                            let uu____20083 =
                                              let uu____20084 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____20084.FStar_Syntax_Syntax.n
                                               in
                                            match uu____20083 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2599_20109 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2599_20109.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2599_20109.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  }  in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1
                                                   in
                                                let subst1 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst  in
                                                ((a1, imp_a), subst1,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____20132 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____20146 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____20146 with
                                                 | (a1,uu____20174,g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g
                                                        in
                                                     let subst1 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst  in
                                                     ((a1, imp_a), subst1,
                                                       bvs, g1))
                                            | uu____20198 ->
                                                fail "Not a simple pattern"
                                             in
                                          (match uu____20062 with
                                           | (a1,subst1,bvs1,g) ->
                                               let uu____20263 =
                                                 let uu____20286 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20286)
                                                  in
                                               aux uu____20263 formals2 args2)
                                      | uu____20325 ->
                                          fail "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20384 -> fail "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____20450 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____20450
           then
             let uu____20455 = FStar_Syntax_Print.pat_to_string p  in
             let uu____20457 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20455
               uu____20457
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20482 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____20482 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____20493 =
                 let uu____20498 =
                   let uu____20499 =
                     let uu____20508 =
                       let uu____20509 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____20509
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____20508
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____20499]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____20498  in
               uu____20493 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____20545 =
                 let uu____20550 =
                   let uu____20551 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____20551]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20550  in
               uu____20545 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20613 ->
               let uu____20620 =
                 let uu____20622 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20622
                  in
               failwith uu____20620
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2638_20644 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2638_20644.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2638_20644.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20645 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____20645,
                 (let uu___2641_20652 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2641_20652.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2645_20656 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2645_20656.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2645_20656.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20657 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____20657,
                 (let uu___2648_20664 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2648_20664.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____20666 ->
               let uu____20667 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____20667 with
                | (uu____20696,e_c,uu____20698,uu____20699) ->
                    let uu____20704 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____20704 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____20734 =
                              let uu____20736 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____20736  in
                            if uu____20734
                            then
                              let uu____20739 =
                                let uu____20741 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____20743 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20741 uu____20743
                                 in
                              fail uu____20739
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20805  ->
                        match uu____20805 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20835
                                 -> (p1, b)
                             | uu____20845 ->
                                 let uu____20846 =
                                   let uu____20849 =
                                     let uu____20850 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____20850
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____20849
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____20846, b))) sub_pats
                    in
                 let uu___2676_20854 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2676_20854.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20899  ->
                         match uu____20899 with
                         | (x,uu____20909) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20917
                                  -> false
                              | uu____20925 -> true)))
                  in
               let uu____20927 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____20927 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20971 =
                          let uu____20973 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____20975 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____20977 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____20984 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20973 uu____20975 uu____20977 uu____20984
                           in
                        failwith uu____20971)
                     else ();
                     (let uu____20989 =
                        let uu____21001 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____21001 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable)
                            ->
                            let g' =
                              let uu____21038 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21038  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21041 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21041
                              then
                                let uu____21046 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21048 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21050 =
                                  let uu____21052 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21060 =
                                           let uu____21062 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21064 =
                                             let uu____21066 =
                                               let uu____21068 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21068 ")"
                                                in
                                             Prims.op_Hat " : " uu____21066
                                              in
                                           Prims.op_Hat uu____21062
                                             uu____21064
                                            in
                                         Prims.op_Hat "(" uu____21060)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21052
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21046 uu____21048 uu____21050
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable))
                         in
                      match uu____20989 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable) ->
                          let uu____21111 =
                            let uu____21143 =
                              let uu____21175 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21175, erasable,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21257  ->
                                 fun uu____21258  ->
                                   fun x  ->
                                     match (uu____21257, uu____21258) with
                                     | ((env2,bvs,tms,pats,subst,g,erasable1,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____21442 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____21442 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21512 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21512 i
                                                   in
                                                let uu____21513 =
                                                  let uu____21522 =
                                                    let uu____21527 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____21527  in
                                                  FStar_List.map uu____21522
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____21513
                                                 in
                                              let uu____21533 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst),
                                                uu____21533,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21143 sub_pats1 simple_bvs1
                             in
                          (match uu____21111 with
                           | (_env,bvs,tms,checked_sub_pats,subst,g,erasable1,uu____21592)
                               ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst simple_pat_e1
                                  in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd,b)::simple_pats1 ->
                                       (match hd.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x,e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst
                                                e
                                               in
                                            let hd1 =
                                              let uu___2760_21768 = hd  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2760_21768.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____21773 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd1, b) :: uu____21773
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd1,uu____21817)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21854 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd1, b) :: uu____21854
                                             | uu____21874 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21900 ->
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
                                     let uu___2781_21943 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2781_21943.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21955 -> failwith "Impossible"  in
                               let uu____21959 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____21959, g, erasable1))))))
           in
        (let uu____21966 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____21966
         then
           let uu____21971 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21971
         else ());
        (let uu____21976 =
           let uu____21994 =
             let uu___2786_21995 =
               let uu____21996 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____21996 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2786_21995.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2786_21995.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2786_21995.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2786_21995.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2786_21995.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2786_21995.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2786_21995.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2786_21995.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2786_21995.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2786_21995.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2786_21995.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2786_21995.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2786_21995.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2786_21995.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2786_21995.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2786_21995.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2786_21995.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2786_21995.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2786_21995.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2786_21995.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2786_21995.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2786_21995.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2786_21995.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2786_21995.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2786_21995.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2786_21995.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2786_21995.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2786_21995.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2786_21995.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2786_21995.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2786_21995.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2786_21995.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2786_21995.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2786_21995.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2786_21995.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2786_21995.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2786_21995.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2786_21995.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2786_21995.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2786_21995.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2786_21995.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2786_21995.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2786_21995.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2786_21995.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2786_21995.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____22012 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____21994 uu____22012 pat_t  in
         match uu____21976 with
         | (bvs,tms,pat_e,pat,g,erasable) ->
             ((let uu____22051 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22051
               then
                 let uu____22056 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22058 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22056
                   uu____22058
               else ());
              (let uu____22063 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22064 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22063, pat_e, uu____22064, g, erasable))))

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
      fun branch  ->
        let uu____22102 = FStar_Syntax_Subst.open_branch branch  in
        match uu____22102 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22151 = branch  in
            (match uu____22151 with
             | (cpat,uu____22182,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22204 =
                   let uu____22211 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22211
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22204 with
                  | (scrutinee_env,uu____22248) ->
                      let uu____22253 = tc_pat env pat_t pattern  in
                      (match uu____22253 with
                       | (pattern1,pat_bvs,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable)
                           ->
                           ((let uu____22323 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____22323
                             then
                               let uu____22327 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____22329 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs
                                  in
                               let uu____22332 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____22341 =
                                          let uu____22343 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____22343  in
                                        Prims.op_Hat s uu____22341) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____22327 uu____22329 uu____22332
                             else ());
                            (let uu____22350 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____22380 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____22380
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____22403 =
                                        let uu____22410 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____22410 e  in
                                      match uu____22403 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____22350 with
                             | (when_clause1,g_when) ->
                                 let uu____22467 = tc_term pat_env branch_exp
                                    in
                                 (match uu____22467 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____22526 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun uu____22537  ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____22537) uu____22526
                                           in
                                        let branch_guard =
                                          let uu____22541 =
                                            let uu____22543 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____22543  in
                                          if uu____22541
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22599 =
                                                   let uu____22607 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22607
                                                    in
                                                 match uu____22599 with
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
                                                       let uu____22623 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____22623
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____22644 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____22660
                                                                =
                                                                let uu____22665
                                                                  =
                                                                  let uu____22666
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                  [uu____22666]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc
                                                                  uu____22665
                                                                 in
                                                              uu____22660
                                                                FStar_Pervasives_Native.None
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____22691 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____22691])
                                                     else []
                                                  in
                                               let fail uu____22699 =
                                                 let uu____22700 =
                                                   let uu____22702 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____22704 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____22706 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22702 uu____22704
                                                     uu____22706
                                                    in
                                                 failwith uu____22700  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____22721) ->
                                                     head_constructor t1
                                                 | uu____22726 -> fail ()  in
                                               let force_scrutinee
                                                 uu____22732 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____22733 =
                                                       let uu____22735 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____22737 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22735
                                                         uu____22737
                                                        in
                                                     failwith uu____22733
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____22744 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____22744
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22749,FStar_Syntax_Syntax.Tm_name
                                                  uu____22750) -> []
                                               | (uu____22751,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22754 =
                                                     let uu____22755 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____22756 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____22755
                                                       uu____22756 pat_exp2
                                                      in
                                                   [uu____22754]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22757,FStar_Pervasives_Native.Some
                                                   uu____22758)),uu____22759)
                                                   ->
                                                   let uu____22776 =
                                                     let uu____22783 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____22783 with
                                                     | (env1,uu____22797) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____22776 with
                                                    | (uu____22804,t,uu____22806)
                                                        ->
                                                        let uu____22807 =
                                                          let uu____22808 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____22808
                                                            pat_exp2
                                                           in
                                                        [uu____22807])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22809,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22810) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22834 =
                                                     let uu____22836 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22836
                                                      in
                                                   if uu____22834
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22846 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22849 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22846
                                                        uu____22849)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22852,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22853) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22871 =
                                                     let uu____22873 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22873
                                                      in
                                                   if uu____22871
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22883 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22886 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22883
                                                        uu____22886)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22889,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head,args)) ->
                                                   let f =
                                                     head_constructor head
                                                      in
                                                   let uu____22936 =
                                                     (let uu____22940 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____22940)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____22936
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22968 =
                                                          let uu____22973 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____22973
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23059
                                                                     ->
                                                                    match uu____23059
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23081),
                                                                    (ei,uu____23083))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23111
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23111
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23132
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23144
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23144
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23146
                                                                    =
                                                                    let uu____23147
                                                                    =
                                                                    let uu____23152
                                                                    =
                                                                    let uu____23153
                                                                    =
                                                                    let uu____23162
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23162
                                                                     in
                                                                    [uu____23153]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23152
                                                                     in
                                                                    uu____23147
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23146
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____22968
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23185 =
                                                        let uu____23188 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23188 f
                                                         in
                                                      FStar_List.append
                                                        uu____23185
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23191,uu____23192) ->
                                                   []
                                               | uu____23199 ->
                                                   let uu____23204 =
                                                     let uu____23206 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23208 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23206
                                                       uu____23208
                                                      in
                                                   failwith uu____23204
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23237 =
                                                 let uu____23239 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23239
                                                  in
                                               if uu____23237
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23245 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23245
                                                     in
                                                  let uu____23254 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23254 with
                                                  | (k,uu____23260) ->
                                                      let uu____23261 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                          ""
                                                         in
                                                      (match uu____23261 with
                                                       | (t1,uu____23270,uu____23271)
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
                                        let uu____23285 =
                                          let eqs =
                                            let uu____23305 =
                                              let uu____23307 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____23307
                                               in
                                            if uu____23305
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____23317 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____23330 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____23331 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____23332 ->
                                                   let uu____23333 =
                                                     let uu____23334 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____23334 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____23333)
                                             in
                                          let uu____23335 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____23335 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____23364 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____23364
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____23366 =
                                                let env1 =
                                                  let uu____23372 =
                                                    FStar_All.pipe_right
                                                      pat_bvs
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____23372
                                                   in
                                                if branch_has_layered_effect
                                                then
                                                  let c2 =
                                                    FStar_TypeChecker_Util.weaken_precondition
                                                      env1 c1
                                                      (FStar_TypeChecker_Common.NonTrivial
                                                         branch_guard)
                                                     in
                                                  (c2,
                                                    FStar_TypeChecker_Env.trivial_guard)
                                                else
                                                  (match (eqs,
                                                           when_condition)
                                                   with
                                                   | uu____23393 when
                                                       let uu____23404 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____23404
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
                                                       let uu____23425 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____23426 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____23425,
                                                         uu____23426)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____23441 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____23441
                                                          in
                                                       let uu____23442 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____23443 =
                                                         let uu____23444 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____23444 g_when
                                                          in
                                                       (uu____23442,
                                                         uu____23443)
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
                                                       let uu____23458 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____23458, g_when))
                                                 in
                                              (match uu____23366 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return =
                                                     let c_weak1 =
                                                       let uu____23501 =
                                                         should_return &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____23501
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____23508 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____23508
                                                         then
                                                           FStar_Util.print_string
                                                             "Typechecking pat_bv_tms ...\n"
                                                         else ());
                                                        (let pat_bv_tms1 =
                                                           FStar_All.pipe_right
                                                             pat_bv_tms
                                                             (FStar_List.map
                                                                (fun
                                                                   pat_bv_tm 
                                                                   ->
                                                                   let uu____23528
                                                                    =
                                                                    let uu____23533
                                                                    =
                                                                    let uu____23534
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____23534]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____23533
                                                                     in
                                                                   uu____23528
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                            in
                                                         let pat_bv_tms2 =
                                                           let env1 =
                                                             let uu___3026_23571
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee
                                                                in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.use_eq_strict
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.use_eq_strict);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.mpreprocess
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.mpreprocess);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___3026_23571.FStar_TypeChecker_Env.erasable_types_tab)
                                                             }  in
                                                           let uu____23573 =
                                                             let uu____23576
                                                               =
                                                               FStar_List.fold_left2
                                                                 (fun
                                                                    uu____23604
                                                                     ->
                                                                    fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    fun bv 
                                                                    ->
                                                                    match uu____23604
                                                                    with
                                                                    | 
                                                                    (substs,acc)
                                                                    ->
                                                                    let expected_t
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    substs
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____23645
                                                                    =
                                                                    let uu____23652
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs)
                                                                     in
                                                                    let uu____23653
                                                                    =
                                                                    let uu____23664
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t
                                                                     in
                                                                    tc_trivial_guard
                                                                    uu____23664
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23652
                                                                    uu____23653
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23645
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    ((FStar_List.append
                                                                    substs
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv,
                                                                    pat_bv_tm1)]),
                                                                    (FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])))
                                                                 ([], [])
                                                                 pat_bv_tms1
                                                                 pat_bvs
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____23576
                                                               FStar_Pervasives_Native.snd
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____23573
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env1))
                                                            in
                                                         (let uu____23726 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____23726
                                                          then
                                                            let uu____23731 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____23740
                                                                    =
                                                                    let uu____23742
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23742
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23740)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            let uu____23746 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____23755
                                                                    =
                                                                    let uu____23757
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23757
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23755)
                                                                "" pat_bvs
                                                               in
                                                            FStar_Util.print2
                                                              "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                              uu____23731
                                                              uu____23746
                                                          else ());
                                                         (let uu____23764 =
                                                            FStar_All.pipe_right
                                                              c_weak1
                                                              (FStar_TypeChecker_Common.apply_lcomp
                                                                 (fun c2  ->
                                                                    c2)
                                                                 (fun g  ->
                                                                    match eqs
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> g
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eqs1 ->
                                                                    FStar_TypeChecker_Common.weaken_guard_formula
                                                                    g eqs1))
                                                             in
                                                          let uu____23771 =
                                                            let uu____23776 =
                                                              FStar_TypeChecker_Env.push_bv
                                                                env scrutinee
                                                               in
                                                            FStar_TypeChecker_Util.close_layered_lcomp
                                                              uu____23776
                                                              pat_bvs
                                                              pat_bv_tms2
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23764
                                                            uu____23771)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs c_weak1
                                                      in
                                                   let uu____23779 =
                                                     FStar_TypeChecker_Env.close_guard
                                                       env binders
                                                       g_when_weak
                                                      in
                                                   let uu____23780 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_pat g_branch1
                                                      in
                                                   ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                     (c_weak.FStar_TypeChecker_Common.cflags),
                                                     maybe_return_c_weak,
                                                     uu____23779,
                                                     uu____23780))
                                           in
                                        match uu____23285 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____23835 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____23835
                                              then
                                                let uu____23838 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____23838
                                              else ());
                                             (let uu____23844 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____23861 =
                                                let uu____23862 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____23862 guard
                                                 in
                                              (uu____23844, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____23861,
                                                erasable)))))))))))

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
          let uu____23911 = check_let_bound_def true env1 lb  in
          (match uu____23911 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____23937 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23959 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____23959, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23965 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____23965
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____23966 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____23966 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____23984 =
                          let uu____23997 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____23997  in
                        (match uu____23984 with
                         | (uu____24047,univs,e11,c11,gvs) ->
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
                             let uu____24061 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs, uu____24061)))
                  in
               (match uu____23937 with
                | (g11,e11,univ_vars1,c11) ->
                    let uu____24078 =
                      let uu____24087 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24087
                      then
                        let uu____24098 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24098 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24132 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24132
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24133 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24133, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24145 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24145 with
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
                                  let uu____24169 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24169
                                  then e2
                                  else
                                    ((let uu____24177 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24177
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
                    (match uu____24078 with
                     | (e21,c12) ->
                         ((let uu____24201 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24201
                           then
                             let uu____24204 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24204
                           else ());
                          (let e12 =
                             let uu____24210 = FStar_Options.tcnorm ()  in
                             if uu____24210
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
                           (let uu____24216 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24216
                            then
                              let uu____24219 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24219
                            else ());
                           (let cres =
                              let uu____24225 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24225
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
                                   | (wp,uu____24233)::[] -> wp
                                   | uu____24258 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let ret =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator
                                      in
                                   let uu____24275 =
                                     let uu____24280 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl ret
                                        in
                                     let uu____24281 =
                                       let uu____24282 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____24291 =
                                         let uu____24302 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____24302]  in
                                       uu____24282 :: uu____24291  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24280 uu____24281
                                      in
                                   uu____24275 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____24339 =
                                     let uu____24344 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl bind
                                        in
                                     let uu____24345 =
                                       let uu____24346 =
                                         let uu____24355 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____24355
                                          in
                                       let uu____24364 =
                                         let uu____24375 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____24392 =
                                           let uu____24403 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____24412 =
                                             let uu____24423 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____24432 =
                                               let uu____24443 =
                                                 let uu____24452 =
                                                   let uu____24453 =
                                                     let uu____24454 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____24454]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____24453 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____24452
                                                  in
                                               [uu____24443]  in
                                             uu____24423 :: uu____24432  in
                                           uu____24403 :: uu____24412  in
                                         uu____24375 :: uu____24392  in
                                       uu____24346 :: uu____24364  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24344 uu____24345
                                      in
                                   uu____24339 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____24531 =
                                   let uu____24532 =
                                     let uu____24543 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____24543]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____24532;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____24531)
                               in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars1
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos
                               in
                            let uu____24571 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____24585 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____24571, uu____24585,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____24586 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____24597 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____24597
        then
          let universe_of_binders bs =
            let uu____24624 =
              FStar_List.fold_left
                (fun uu____24649  ->
                   fun b  ->
                     match uu____24649 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____24624 with | (uu____24697,us) -> FStar_List.rev us
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
            let uu___3158_24733 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3158_24733.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3158_24733.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3158_24733.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3158_24733.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3158_24733.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3158_24733.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3158_24733.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3158_24733.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3158_24733.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3158_24733.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3158_24733.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3158_24733.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3158_24733.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3158_24733.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3158_24733.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3158_24733.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3158_24733.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3158_24733.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3158_24733.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3158_24733.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3158_24733.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3158_24733.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3158_24733.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3158_24733.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3158_24733.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3158_24733.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3158_24733.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3158_24733.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3158_24733.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3158_24733.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3158_24733.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3158_24733.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3158_24733.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3158_24733.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3158_24733.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3158_24733.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3158_24733.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3158_24733.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3158_24733.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3158_24733.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3158_24733.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3158_24733.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3158_24733.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3158_24733.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3158_24733.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____24735 =
            let uu____24747 =
              let uu____24748 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____24748 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____24747 lb  in
          (match uu____24735 with
           | (e1,uu____24771,c1,g1,annotated) ->
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
                  (let uu____24785 =
                     let uu____24791 =
                       let uu____24793 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____24795 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24793 uu____24795
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24791)
                      in
                   FStar_Errors.raise_error uu____24785
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24806 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____24806
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3173_24818 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3173_24818.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3173_24818.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____24819 =
                   let uu____24824 =
                     let uu____24825 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____24825]  in
                   FStar_Syntax_Subst.open_term uu____24824 e2  in
                 match uu____24819 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____24869 =
                       let uu____24876 = tc_term env_x e21  in
                       FStar_All.pipe_right uu____24876
                         (fun uu____24902  ->
                            match uu____24902 with
                            | (e22,c2,g2) ->
                                let uu____24918 =
                                  let uu____24923 =
                                    FStar_All.pipe_right
                                      (fun uu____24941  ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____24947  ->
                                         FStar_Pervasives_Native.Some
                                           uu____24947)
                                     in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____24923 env_x e22 c2 g2
                                   in
                                (match uu____24918 with
                                 | (c21,g21) -> (e22, c21, g21)))
                        in
                     (match uu____24869 with
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
                            let uu____24975 =
                              let uu____24982 =
                                let uu____24983 =
                                  let uu____24997 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____24997)  in
                                FStar_Syntax_Syntax.Tm_let uu____24983  in
                              FStar_Syntax_Syntax.mk uu____24982  in
                            uu____24975 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let g21 =
                            let uu____25015 =
                              let uu____25017 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____25017
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____25015 xb g2
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21
                             in
                          let uu____25020 =
                            let uu____25022 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____25022  in
                          if uu____25020
                          then
                            let tt =
                              let uu____25033 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____25033
                                FStar_Option.get
                               in
                            ((let uu____25039 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25039
                              then
                                let uu____25044 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25046 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25044 uu____25046
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25053 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25053 with
                             | (t,g_ex) ->
                                 ((let uu____25067 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25067
                                   then
                                     let uu____25072 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25074 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25072 uu____25074
                                   else ());
                                  (let uu____25079 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3212_25081 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3212_25081.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3212_25081.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3212_25081.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25079))))))))
      | uu____25082 ->
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
          let uu____25118 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25118 with
           | (lbs1,e21) ->
               let uu____25137 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25137 with
                | (env0,topt) ->
                    let uu____25156 = build_let_rec_env true env0 lbs1  in
                    (match uu____25156 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25179 = check_let_recs rec_env lbs2  in
                         (match uu____25179 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25199 =
                                  let uu____25200 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25200
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25199
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25206 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25206
                                  (fun uu____25223  ->
                                     FStar_Pervasives_Native.Some uu____25223)
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
                                     let uu____25260 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____25294 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____25294)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25260
                                      in
                                   FStar_List.map2
                                     (fun uu____25329  ->
                                        fun lb  ->
                                          match uu____25329 with
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
                                let uu____25377 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____25377
                                 in
                              let uu____25378 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____25378 with
                               | (lbs5,e22) ->
                                   ((let uu____25398 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____25398
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____25399 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____25399, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____25413 -> failwith "Impossible"

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
          let uu____25449 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25449 with
           | (lbs1,e21) ->
               let uu____25468 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25468 with
                | (env0,topt) ->
                    let uu____25487 = build_let_rec_env false env0 lbs1  in
                    (match uu____25487 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25510 =
                           let uu____25517 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____25517
                             (fun uu____25540  ->
                                match uu____25540 with
                                | (lbs3,g) ->
                                    let uu____25559 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____25559))
                            in
                         (match uu____25510 with
                          | (lbs3,g_lbs) ->
                              let uu____25574 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3287_25597 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3287_25597.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3287_25597.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3290_25599 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3290_25599.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____25574 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____25626 = tc_term env2 e21  in
                                   (match uu____25626 with
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
                                          let uu____25650 =
                                            let uu____25651 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____25651 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____25650
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
                                          let uu___3311_25661 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3311_25661.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3311_25661.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3311_25661.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____25669 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____25669))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____25671 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____25671 with
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
                                                  uu____25712 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____25713 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____25713 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3327_25727
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3327_25727.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3327_25727.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3327_25727.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____25728 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____25728))))))))))
      | uu____25729 -> failwith "Impossible"

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
          let uu____25777 = FStar_Options.ml_ish ()  in
          if uu____25777
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____25785 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____25785 with
             | (formals,c) ->
                 let uu____25793 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____25793 with
                  | (actuals,uu____25804,uu____25805) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____25826 =
                          let uu____25832 =
                            let uu____25834 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____25836 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____25834 uu____25836
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____25832)
                           in
                        FStar_Errors.raise_error uu____25826
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____25844 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____25844 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n = FStar_List.length actuals1  in
                              if n = Prims.int_one
                              then "1 argument was found"
                              else
                                (let uu____25875 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____25875)
                               in
                            let formals_msg =
                              let n = FStar_List.length formals  in
                              if n = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____25894 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments"
                                   uu____25894)
                               in
                            let msg =
                              let uu____25899 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____25901 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____25899 uu____25901 formals_msg
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
        let uu____25913 =
          FStar_List.fold_left
            (fun uu____25946  ->
               fun lb  ->
                 match uu____25946 with
                 | (lbs1,env1,g_acc) ->
                     let uu____25971 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____25971 with
                      | (univ_vars,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____25994 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars
                                  in
                               let uu____26013 =
                                 let uu____26020 =
                                   let uu____26021 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____26021
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3373_26032 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3373_26032.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3373_26032.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3373_26032.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3373_26032.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3373_26032.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3373_26032.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3373_26032.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3373_26032.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3373_26032.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3373_26032.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3373_26032.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3373_26032.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3373_26032.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3373_26032.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3373_26032.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3373_26032.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3373_26032.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3373_26032.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3373_26032.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3373_26032.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3373_26032.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3373_26032.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3373_26032.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3373_26032.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3373_26032.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3373_26032.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3373_26032.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3373_26032.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3373_26032.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3373_26032.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3373_26032.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3373_26032.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3373_26032.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3373_26032.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3373_26032.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3373_26032.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3373_26032.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3373_26032.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3373_26032.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3373_26032.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3373_26032.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3373_26032.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3373_26032.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3373_26032.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3373_26032.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____26020 ""
                                  in
                               match uu____26013 with
                               | (t1,uu____26042,g) ->
                                   let uu____26044 =
                                     let uu____26045 =
                                       let uu____26046 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26046
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26045
                                      in
                                   let uu____26047 = norm env01 t1  in
                                   (uu____26044, uu____26047))
                             in
                          (match uu____25994 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____26067 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____26067
                                 then
                                   let uu___3383_26070 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3383_26070.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3383_26070.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3383_26070.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3383_26070.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3383_26070.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3383_26070.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3383_26070.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3383_26070.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3383_26070.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3383_26070.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3383_26070.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3383_26070.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3383_26070.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3383_26070.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3383_26070.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3383_26070.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___3383_26070.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3383_26070.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3383_26070.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3383_26070.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3383_26070.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3383_26070.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3383_26070.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3383_26070.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3383_26070.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3383_26070.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3383_26070.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3383_26070.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3383_26070.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3383_26070.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3383_26070.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3383_26070.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3383_26070.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3383_26070.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3383_26070.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___3383_26070.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3383_26070.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___3383_26070.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3383_26070.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3383_26070.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3383_26070.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3383_26070.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3383_26070.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3383_26070.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3383_26070.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars, t1)
                                  in
                               let lb1 =
                                 let uu___3386_26084 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3386_26084.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3386_26084.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3386_26084.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3386_26084.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____25913 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26110 =
        let uu____26119 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26145 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26145 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26175 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26175
                       | uu____26182 ->
                           let lb1 =
                             let uu___3403_26185 = lb  in
                             let uu____26186 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26186;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3403_26185.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____26189 =
                             let uu____26196 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____26196
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____26189 with
                            | (e,c,g) ->
                                ((let uu____26205 =
                                    let uu____26207 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____26207  in
                                  if uu____26205
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
        FStar_All.pipe_right uu____26119 FStar_List.unzip  in
      match uu____26110 with
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
        let uu____26263 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____26263 with
        | (env1,uu____26282) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____26290 = check_lbtyp top_level env lb  in
            (match uu____26290 with
             | (topt,wf_annot,univ_vars,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____26339 =
                     tc_maybe_toplevel_term
                       (let uu___3434_26348 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3434_26348.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3434_26348.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3434_26348.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3434_26348.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3434_26348.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3434_26348.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3434_26348.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3434_26348.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3434_26348.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3434_26348.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3434_26348.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3434_26348.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3434_26348.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3434_26348.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3434_26348.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3434_26348.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3434_26348.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3434_26348.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3434_26348.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3434_26348.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3434_26348.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3434_26348.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3434_26348.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3434_26348.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3434_26348.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3434_26348.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3434_26348.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3434_26348.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3434_26348.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3434_26348.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3434_26348.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3434_26348.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3434_26348.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3434_26348.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3434_26348.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3434_26348.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3434_26348.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3434_26348.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3434_26348.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3434_26348.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3434_26348.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3434_26348.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3434_26348.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3434_26348.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3434_26348.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____26339 with
                   | (e12,c1,g1) ->
                       let uu____26363 =
                         let uu____26368 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____26374  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____26368 e12 c1 wf_annot
                          in
                       (match uu____26363 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____26391 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____26391
                              then
                                let uu____26394 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____26396 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____26398 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____26394 uu____26396 uu____26398
                              else ());
                             (e12, univ_vars, c11, g11,
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
            let uu____26437 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26437 with
             | (univ_opening,univ_vars) ->
                 let uu____26470 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____26470))
        | uu____26475 ->
            let uu____26476 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26476 with
             | (univ_opening,univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____26526 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____26526)
                 else
                   (let uu____26533 = FStar_Syntax_Util.type_u ()  in
                    match uu____26533 with
                    | (k,uu____26553) ->
                        let uu____26554 =
                          tc_check_tot_or_gtot_term env1 t1 k ""  in
                        (match uu____26554 with
                         | (t2,uu____26577,g) ->
                             ((let uu____26580 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____26580
                               then
                                 let uu____26583 =
                                   let uu____26585 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____26585
                                    in
                                 let uu____26586 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____26583 uu____26586
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____26592 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____26592))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____26598  ->
      match uu____26598 with
      | (x,imp) ->
          let uu____26625 = FStar_Syntax_Util.type_u ()  in
          (match uu____26625 with
           | (tu,u) ->
               ((let uu____26647 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____26647
                 then
                   let uu____26650 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____26652 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____26654 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____26650 uu____26652 uu____26654
                 else ());
                (let uu____26659 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu ""
                    in
                 match uu____26659 with
                 | (t,uu____26682,g) ->
                     let uu____26684 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____26700 =
                             tc_tactic FStar_Syntax_Syntax.t_unit
                               FStar_Syntax_Syntax.t_unit env tau
                              in
                           (match uu____26700 with
                            | (tau1,uu____26714,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____26718 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____26684 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3496_26753 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3496_26753.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3496_26753.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____26755 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____26755
                            then
                              let uu____26758 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____26762 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26758
                                uu____26762
                            else ());
                           (let uu____26767 = push_binding env x1  in
                            (x1, uu____26767, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____26779 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____26779
       then
         let uu____26782 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____26782
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26895 = tc_binder env1 b  in
             (match uu____26895 with
              | (b1,env',g,u) ->
                  let uu____26944 = aux env' bs2  in
                  (match uu____26944 with
                   | (bs3,env'1,g',us) ->
                       let uu____27005 =
                         let uu____27006 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____27006  in
                       ((b1 :: bs3), env'1, uu____27005, (u :: us))))
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
          (fun uu____27114  ->
             fun uu____27115  ->
               match (uu____27114, uu____27115) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____27207 = tc_term en1 t  in
                     match uu____27207 with
                     | (t1,uu____27227,g') ->
                         let uu____27229 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____27229)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____27283  ->
             match uu____27283 with
             | (pats1,g) ->
                 let uu____27310 = tc_args en p  in
                 (match uu____27310 with
                  | (args,g') ->
                      let uu____27323 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____27323))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      Prims.string ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun msg  ->
        let uu____27338 = tc_maybe_toplevel_term env e  in
        match uu____27338 with
        | (e1,c,g) ->
            let uu____27354 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
               in
            if uu____27354
            then (e1, c, g)
            else
              (let g1 =
                 FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
               let uu____27366 = FStar_TypeChecker_Common.lcomp_comp c  in
               match uu____27366 with
               | (c1,g_c) ->
                   let c2 = norm_c env c1  in
                   let uu____27380 =
                     let uu____27386 =
                       FStar_TypeChecker_Util.is_pure_effect env
                         (FStar_Syntax_Util.comp_effect_name c2)
                        in
                     if uu____27386
                     then
                       let uu____27394 =
                         FStar_Syntax_Syntax.mk_Total
                           (FStar_Syntax_Util.comp_result c2)
                          in
                       (uu____27394, false)
                     else
                       (let uu____27399 =
                          FStar_Syntax_Syntax.mk_GTotal
                            (FStar_Syntax_Util.comp_result c2)
                           in
                        (uu____27399, true))
                      in
                   (match uu____27380 with
                    | (target_comp,allow_ghost) ->
                        let uu____27412 =
                          FStar_TypeChecker_Rel.sub_comp env c2 target_comp
                           in
                        (match uu____27412 with
                         | FStar_Pervasives_Native.Some g' ->
                             let uu____27422 =
                               FStar_TypeChecker_Common.lcomp_of_comp
                                 target_comp
                                in
                             let uu____27423 =
                               let uu____27424 =
                                 FStar_TypeChecker_Env.conj_guard g_c g'  in
                               FStar_TypeChecker_Env.conj_guard g1
                                 uu____27424
                                in
                             (e1, uu____27422, uu____27423)
                         | uu____27425 ->
                             if allow_ghost
                             then
                               let uu____27435 =
                                 FStar_TypeChecker_Err.expected_ghost_expression
                                   e1 c2 msg
                                  in
                               FStar_Errors.raise_error uu____27435
                                 e1.FStar_Syntax_Syntax.pos
                             else
                               (let uu____27449 =
                                  FStar_TypeChecker_Err.expected_pure_expression
                                    e1 c2 msg
                                   in
                                FStar_Errors.raise_error uu____27449
                                  e1.FStar_Syntax_Syntax.pos))))

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  = fun env  -> fun e  -> tc_tot_or_gtot_term' env e ""

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.string ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        fun msg  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
          tc_tot_or_gtot_term' env1 e msg

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____27478 = tc_tot_or_gtot_term env t  in
      match uu____27478 with
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
        let uu____27509 = tc_check_tot_or_gtot_term env t k ""  in
        match uu____27509 with
        | (t1,uu____27518,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____27539 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____27539
       then
         let uu____27544 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____27544
       else ());
      (let env1 =
         let uu___3592_27550 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3592_27550.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3592_27550.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3592_27550.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3592_27550.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3592_27550.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3592_27550.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3592_27550.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3592_27550.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3592_27550.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3592_27550.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3592_27550.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3592_27550.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3592_27550.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3592_27550.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3592_27550.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3592_27550.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3592_27550.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3592_27550.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3592_27550.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3592_27550.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3592_27550.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3592_27550.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3592_27550.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3592_27550.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3592_27550.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3592_27550.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3592_27550.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3592_27550.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3592_27550.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3592_27550.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3592_27550.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3592_27550.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3592_27550.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3592_27550.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3592_27550.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3592_27550.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3592_27550.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3592_27550.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3592_27550.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3592_27550.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3592_27550.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3592_27550.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3592_27550.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3592_27550.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____27558 =
         try
           (fun uu___3596_27572  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____27593) ->
             let uu____27596 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____27596
          in
       match uu____27558 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____27614 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____27614
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____27625 =
                let uu____27631 =
                  let uu____27633 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____27633
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____27631)
                 in
              let uu____27637 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____27625 uu____27637))
  
let level_of_type_fail :
  'uuuuuu27653 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu27653
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____27671 =
          let uu____27677 =
            let uu____27679 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____27679 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____27677)  in
        let uu____27683 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____27671 uu____27683
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____27717 =
            let uu____27718 = FStar_Syntax_Util.unrefine t1  in
            uu____27718.FStar_Syntax_Syntax.n  in
          match uu____27717 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____27722 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____27728 = FStar_Syntax_Util.type_u ()  in
                 match uu____27728 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3628_27736 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3628_27736.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3628_27736.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3628_27736.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3628_27736.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3628_27736.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3628_27736.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3628_27736.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3628_27736.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3628_27736.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3628_27736.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3628_27736.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3628_27736.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3628_27736.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3628_27736.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3628_27736.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3628_27736.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3628_27736.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3628_27736.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3628_27736.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3628_27736.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3628_27736.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3628_27736.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3628_27736.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3628_27736.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3628_27736.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3628_27736.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3628_27736.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3628_27736.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3628_27736.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3628_27736.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3628_27736.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3628_27736.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3628_27736.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3628_27736.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3628_27736.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3628_27736.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3628_27736.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3628_27736.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3628_27736.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3628_27736.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3628_27736.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3628_27736.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3628_27736.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3628_27736.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3628_27736.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____27741 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____27741
                       | uu____27743 ->
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
      let uu____27760 =
        let uu____27761 = FStar_Syntax_Subst.compress e  in
        uu____27761.FStar_Syntax_Syntax.n  in
      match uu____27760 with
      | FStar_Syntax_Syntax.Tm_bvar uu____27764 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____27767 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____27783 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____27800) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____27845) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27852 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27852 with | ((uu____27861,t),uu____27863) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27869 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____27869
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27872,(FStar_Util.Inl t,uu____27874),uu____27875) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27922,(FStar_Util.Inr c,uu____27924),uu____27925) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27973 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27982;
             FStar_Syntax_Syntax.vars = uu____27983;_},us)
          ->
          let uu____27989 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27989 with
           | ((us',t),uu____28000) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____28007 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____28007)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____28026 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____28028 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28037) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28064 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28064 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28084  ->
                      match uu____28084 with
                      | (b,uu____28092) ->
                          let uu____28097 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28097) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28102 = universe_of_aux env res  in
                 level_of_type env res uu____28102  in
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
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rec type_of_head retry hd1 args1 =
            let hd2 = FStar_Syntax_Subst.compress hd1  in
            match hd2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____28213 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____28229 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____28259 ->
                let uu____28260 = universe_of_aux env hd2  in
                (uu____28260, args1)
            | FStar_Syntax_Syntax.Tm_name uu____28271 ->
                let uu____28272 = universe_of_aux env hd2  in
                (uu____28272, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____28283 ->
                let uu____28296 = universe_of_aux env hd2  in
                (uu____28296, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____28307 ->
                let uu____28314 = universe_of_aux env hd2  in
                (uu____28314, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____28325 ->
                let uu____28352 = universe_of_aux env hd2  in
                (uu____28352, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____28363 ->
                let uu____28370 = universe_of_aux env hd2  in
                (uu____28370, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____28381 ->
                let uu____28382 = universe_of_aux env hd2  in
                (uu____28382, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____28393 ->
                let uu____28408 = universe_of_aux env hd2  in
                (uu____28408, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____28419 ->
                let uu____28426 = universe_of_aux env hd2  in
                (uu____28426, args1)
            | FStar_Syntax_Syntax.Tm_type uu____28437 ->
                let uu____28438 = universe_of_aux env hd2  in
                (uu____28438, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____28449,hd3::uu____28451) ->
                let uu____28516 = FStar_Syntax_Subst.open_branch hd3  in
                (match uu____28516 with
                 | (uu____28531,uu____28532,hd4) ->
                     let uu____28550 = FStar_Syntax_Util.head_and_args hd4
                        in
                     (match uu____28550 with
                      | (hd5,args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____28615 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____28617 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____28617 with
                 | (hd3,args2) -> type_of_head false hd3 args2)
            | uu____28675 ->
                let uu____28676 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____28676 with
                 | (env1,uu____28698) ->
                     let env2 =
                       let uu___3789_28704 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3789_28704.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3789_28704.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3789_28704.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3789_28704.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3789_28704.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3789_28704.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3789_28704.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3789_28704.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3789_28704.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3789_28704.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3789_28704.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3789_28704.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3789_28704.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3789_28704.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3789_28704.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3789_28704.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3789_28704.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3789_28704.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3789_28704.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3789_28704.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3789_28704.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3789_28704.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3789_28704.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3789_28704.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3789_28704.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3789_28704.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3789_28704.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3789_28704.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3789_28704.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3789_28704.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3789_28704.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3789_28704.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3789_28704.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3789_28704.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3789_28704.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3789_28704.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3789_28704.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3789_28704.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3789_28704.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3789_28704.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3789_28704.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3789_28704.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3789_28704.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____28709 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____28709
                       then
                         let uu____28714 =
                           let uu____28716 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____28716  in
                         let uu____28717 =
                           FStar_Syntax_Print.term_to_string hd2  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____28714 uu____28717
                       else ());
                      (let uu____28722 = tc_term env2 hd2  in
                       match uu____28722 with
                       | (uu____28743,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____28744;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____28746;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____28747;_},g)
                           ->
                           ((let uu____28765 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____28765
                               (fun uu____28766  -> ()));
                            (t, args1)))))
             in
          let uu____28777 = type_of_head true hd args  in
          (match uu____28777 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____28816 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____28816 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____28844 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____28844)))
      | FStar_Syntax_Syntax.Tm_match (uu____28846,hd::uu____28848) ->
          let uu____28913 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____28913 with
           | (uu____28914,uu____28915,hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____28933,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____28980 = universe_of_aux env e  in
      level_of_type env e uu____28980
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0  ->
    fun tps  ->
      let uu____29004 = tc_binders env0 tps  in
      match uu____29004 with
      | (tps1,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env0 g; (tps1, env, us))
  
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
      | FStar_Syntax_Syntax.Tm_delayed uu____29062 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29080 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29086 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29086
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29088 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29088
            (fun uu____29102  ->
               match uu____29102 with
               | (t2,uu____29110) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29112;
             FStar_Syntax_Syntax.vars = uu____29113;_},us)
          ->
          let uu____29119 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29119
            (fun uu____29133  ->
               match uu____29133 with
               | (t2,uu____29141) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29142) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29144 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29144
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29146 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29146
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29151;_})
          ->
          let mk_comp =
            let uu____29195 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____29195
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____29226 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____29226
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____29296 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____29296
                 (fun u  ->
                    let uu____29304 =
                      let uu____29307 =
                        let uu____29314 =
                          let uu____29315 =
                            let uu____29330 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____29330)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____29315  in
                        FStar_Syntax_Syntax.mk uu____29314  in
                      uu____29307 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____29304))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____29367 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____29367 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____29426 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____29426
                       (fun uc  ->
                          let uu____29434 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____29434)
                 | (x,imp)::bs3 ->
                     let uu____29460 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____29460
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____29469 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____29489) ->
          let uu____29494 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____29494
            (fun u_x  ->
               let uu____29502 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____29502)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____29507;
             FStar_Syntax_Syntax.vars = uu____29508;_},a::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____29587 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29587 with
           | (unary_op,uu____29607) ->
               let head =
                 let uu____29635 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____29635
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29683;
             FStar_Syntax_Syntax.vars = uu____29684;_},a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____29780 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29780 with
           | (unary_op,uu____29800) ->
               let head =
                 let uu____29828 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   FStar_Pervasives_Native.None uu____29828
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____29884;
             FStar_Syntax_Syntax.vars = uu____29885;_},uu____29886::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29925;
             FStar_Syntax_Syntax.vars = uu____29926;_},(t2,uu____29928)::uu____29929::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let t_hd = type_of_well_typed_term env hd  in
          let rec aux t_hd1 =
            let uu____30025 =
              let uu____30026 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____30026.FStar_Syntax_Syntax.n  in
            match uu____30025 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30099 = FStar_Util.first_N n_args bs  in
                    match uu____30099 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____30187 =
                          let uu____30192 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____30192  in
                        (match uu____30187 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____30246 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____30246 with
                       | (bs1,c1) ->
                           let uu____30267 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____30267
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____30349  ->
                     match uu____30349 with
                     | (bs1,t2) ->
                         let subst =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____30425 = FStar_Syntax_Subst.subst subst t2
                            in
                         FStar_Pervasives_Native.Some uu____30425)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____30427) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____30433,uu____30434) ->
                aux t2
            | uu____30475 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30476,(FStar_Util.Inl t2,uu____30478),uu____30479) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30526,(FStar_Util.Inr c,uu____30528),uu____30529) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____30594 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____30594
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____30602) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____30607 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____30630 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____30644 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____30655 = type_of_well_typed_term env t  in
      match uu____30655 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____30661;
            FStar_Syntax_Syntax.vars = uu____30662;_}
          -> FStar_Pervasives_Native.Some u
      | uu____30665 -> FStar_Pervasives_Native.None

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
            let uu___4068_30693 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4068_30693.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4068_30693.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4068_30693.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4068_30693.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4068_30693.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4068_30693.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4068_30693.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4068_30693.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4068_30693.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4068_30693.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4068_30693.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4068_30693.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4068_30693.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4068_30693.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4068_30693.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4068_30693.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4068_30693.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4068_30693.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4068_30693.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4068_30693.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4068_30693.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4068_30693.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4068_30693.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4068_30693.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4068_30693.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4068_30693.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4068_30693.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4068_30693.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4068_30693.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4068_30693.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4068_30693.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4068_30693.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4068_30693.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4068_30693.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4068_30693.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4068_30693.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4068_30693.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4068_30693.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4068_30693.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4068_30693.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4068_30693.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4068_30693.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4068_30693.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4068_30693.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4068_30693.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30700 =
            if must_total
            then
              let uu____30702 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30702 with | (uu____30709,uu____30710,g) -> g
            else
              (let uu____30714 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30714 with | (uu____30721,uu____30722,g) -> g)
             in
          let uu____30724 = type_of_well_typed_term env2 t  in
          match uu____30724 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____30729 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____30729
                then
                  let uu____30734 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____30736 = FStar_Syntax_Print.term_to_string t  in
                  let uu____30738 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____30740 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____30734 uu____30736 uu____30738 uu____30740
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____30749 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____30749
                 then
                   let uu____30754 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____30756 = FStar_Syntax_Print.term_to_string t  in
                   let uu____30758 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____30760 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____30754
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____30756 uu____30758 uu____30760
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
            let uu___4099_30797 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4099_30797.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4099_30797.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4099_30797.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4099_30797.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4099_30797.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4099_30797.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4099_30797.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4099_30797.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4099_30797.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4099_30797.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4099_30797.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4099_30797.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4099_30797.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4099_30797.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4099_30797.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4099_30797.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4099_30797.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4099_30797.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4099_30797.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4099_30797.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4099_30797.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4099_30797.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4099_30797.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4099_30797.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4099_30797.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4099_30797.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4099_30797.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4099_30797.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4099_30797.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4099_30797.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4099_30797.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4099_30797.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4099_30797.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4099_30797.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4099_30797.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4099_30797.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4099_30797.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4099_30797.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4099_30797.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4099_30797.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4099_30797.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4099_30797.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4099_30797.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4099_30797.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4099_30797.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30804 =
            if must_total
            then
              let uu____30806 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30806 with | (uu____30813,uu____30814,g) -> g
            else
              (let uu____30818 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30818 with | (uu____30825,uu____30826,g) -> g)
             in
          let uu____30828 =
            let uu____30830 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____30830  in
          if uu____30828
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  