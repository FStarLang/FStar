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
      (let uu____3910 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3910
       then
         let uu____3913 =
           let uu____3915 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3915  in
         let uu____3917 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____3919 = FStar_Syntax_Print.term_to_string e  in
         let uu____3921 =
           let uu____3923 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3923  in
         let uu____3924 =
           let uu____3926 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____3926 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3913 uu____3917 uu____3919 uu____3921 uu____3924
       else ());
      (let uu____3935 =
         FStar_Util.record_time
           (fun uu____3954  ->
              tc_maybe_toplevel_term
                (let uu___484_3957 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___484_3957.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___484_3957.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___484_3957.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___484_3957.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___484_3957.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___484_3957.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___484_3957.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___484_3957.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___484_3957.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___484_3957.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___484_3957.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___484_3957.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___484_3957.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___484_3957.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___484_3957.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___484_3957.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___484_3957.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___484_3957.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___484_3957.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___484_3957.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___484_3957.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___484_3957.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___484_3957.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___484_3957.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___484_3957.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___484_3957.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___484_3957.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___484_3957.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___484_3957.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___484_3957.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___484_3957.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___484_3957.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___484_3957.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___484_3957.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___484_3957.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___484_3957.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___484_3957.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___484_3957.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___484_3957.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___484_3957.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___484_3957.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___484_3957.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___484_3957.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___484_3957.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___484_3957.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____3935 with
       | (r,ms) ->
           ((let uu____3982 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3982
             then
               ((let uu____3986 =
                   let uu____3988 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3988
                    in
                 let uu____3990 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3992 =
                   let uu____3994 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3994  in
                 let uu____3995 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3986 uu____3990 uu____3992 uu____3995);
                (let uu____3998 = r  in
                 match uu____3998 with
                 | (e1,lc,uu____4007) ->
                     let uu____4008 =
                       let uu____4010 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4010
                        in
                     let uu____4012 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4014 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4016 =
                       let uu____4018 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4018  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4008 uu____4012 uu____4014 uu____4016))
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
      (let uu____4036 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4036
       then
         let uu____4039 =
           let uu____4041 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4041  in
         let uu____4043 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4045 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4039 uu____4043
           uu____4045
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4056 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4078 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4085 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4098 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4099 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4100 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4101 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4102 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4121 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4136 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4143 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4159 =
             match uu___2_4159 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4165 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name t =
               let uu____4181 =
                 let uu____4182 = FStar_Syntax_Subst.compress t  in
                 uu____4182.FStar_Syntax_Syntax.n  in
               match uu____4181 with
               | FStar_Syntax_Syntax.Tm_name uu____4186 -> true
               | uu____4188 -> false  in
             FStar_Util.for_some
               (fun uu____4198  ->
                  match uu____4198 with
                  | (uu____4204,t) ->
                      let uu____4206 = is_name t  in
                      Prims.op_Negation uu____4206)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4225  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4268  ->
                       match uu____4268 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___557_4297 = qi  in
                  let uu____4298 =
                    FStar_List.map
                      (fun uu____4326  ->
                         match uu____4326 with
                         | ((bv,uu____4342),bv') ->
                             let uu____4354 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4354)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___557_4297.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4298
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
                         let uu____4366 =
                           let uu____4373 =
                             let uu____4374 =
                               let uu____4388 =
                                 let uu____4391 =
                                   let uu____4392 =
                                     let uu____4399 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4399
                                      in
                                   [uu____4392]  in
                                 FStar_Syntax_Subst.close uu____4391 t  in
                               ((false, [lb]), uu____4388)  in
                             FStar_Syntax_Syntax.Tm_let uu____4374  in
                           FStar_Syntax_Syntax.mk uu____4373  in
                         uu____4366 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4435 =
                  FStar_List.fold_right
                    (fun uu____4471  ->
                       fun uu____4472  ->
                         match (uu____4471, uu____4472) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4541 = tc_term env_tm tm  in
                             (match uu____4541 with
                              | (tm1,uu____4559,g) ->
                                  let uu____4561 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4561))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4435 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___585_4603 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___585_4603.FStar_Syntax_Syntax.qkind);
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
                let uu____4614 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4614 with
                 | (env',uu____4628) ->
                     let uu____4633 =
                       tc_term
                         (let uu___594_4642 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___594_4642.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___594_4642.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___594_4642.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___594_4642.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___594_4642.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___594_4642.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___594_4642.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___594_4642.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___594_4642.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___594_4642.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___594_4642.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___594_4642.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___594_4642.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___594_4642.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___594_4642.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___594_4642.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___594_4642.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___594_4642.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___594_4642.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___594_4642.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___594_4642.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___594_4642.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___594_4642.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___594_4642.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___594_4642.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___594_4642.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___594_4642.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___594_4642.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___594_4642.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___594_4642.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___594_4642.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___594_4642.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___594_4642.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___594_4642.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___594_4642.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___594_4642.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___594_4642.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___594_4642.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___594_4642.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___594_4642.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___594_4642.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___594_4642.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___594_4642.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___594_4642.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___594_4642.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4633 with
                      | (qt1,uu____4651,uu____4652) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4658 =
                            let uu____4665 =
                              let uu____4670 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4670  in
                            value_check_expected_typ env1 top uu____4665
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4658 with
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
           { FStar_Syntax_Syntax.blob = uu____4687;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4688;
             FStar_Syntax_Syntax.ltyp = uu____4689;
             FStar_Syntax_Syntax.rng = uu____4690;_}
           ->
           let uu____4701 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4701
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4708 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4708 with
            | (e2,c,g) ->
                let g1 =
                  let uu___624_4725 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___624_4725.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___624_4725.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___624_4725.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4726 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4726, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names,pats)) ->
           let uu____4768 = FStar_Syntax_Util.type_u ()  in
           (match uu____4768 with
            | (t,u) ->
                let uu____4781 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4781 with
                 | (e2,c,g) ->
                     let uu____4797 =
                       let uu____4814 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4814 with
                       | (env2,uu____4838) -> tc_smt_pats env2 pats  in
                     (match uu____4797 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___647_4876 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___647_4876.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___647_4876.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___647_4876.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4877 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4896 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4877, c, uu____4896))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4902 =
             let uu____4903 = FStar_Syntax_Subst.compress e1  in
             uu____4903.FStar_Syntax_Syntax.n  in
           (match uu____4902 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4912,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4914;
                               FStar_Syntax_Syntax.lbtyp = uu____4915;
                               FStar_Syntax_Syntax.lbeff = uu____4916;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4918;
                               FStar_Syntax_Syntax.lbpos = uu____4919;_}::[]),e2)
                ->
                let uu____4950 =
                  let uu____4957 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4957 e11  in
                (match uu____4950 with
                 | (e12,c1,g1) ->
                     let uu____4967 = tc_term env1 e2  in
                     (match uu____4967 with
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
                            let uu____4991 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____4991
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5001 =
                              let uu____5008 =
                                let uu____5009 =
                                  let uu____5023 =
                                    let uu____5031 =
                                      let uu____5034 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____5034]  in
                                    (false, uu____5031)  in
                                  (uu____5023, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____5009  in
                              FStar_Syntax_Syntax.mk uu____5008  in
                            uu____5001 FStar_Pervasives_Native.None
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
                          let uu____5058 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5058)))
            | uu____5059 ->
                let uu____5060 = tc_term env1 e1  in
                (match uu____5060 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5082) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5094) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5113 = tc_term env1 e1  in
           (match uu____5113 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5134,(FStar_Util.Inr expected_c,_tacopt),uu____5137) when
           let uu____5184 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5184 FStar_Util.is_some ->
           let uu____5216 =
             let uu____5227 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5227 FStar_Util.must  in
           (match uu____5216 with
            | (effect_lid,e1,aqual) ->
                let uu____5301 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5301 with
                 | (env0,uu____5315) ->
                     let uu____5320 = tc_comp env0 expected_c  in
                     (match uu____5320 with
                      | (expected_c1,uu____5334,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5338 =
                              let uu____5340 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5340  in
                            if uu____5338
                            then
                              let uu____5343 =
                                let uu____5349 =
                                  let uu____5351 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5353 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5351 uu____5353
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5349)
                                 in
                              FStar_Errors.raise_error uu____5343
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5360 =
                              let uu____5362 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5362  in
                            if uu____5360
                            then
                              let uu____5365 =
                                let uu____5371 =
                                  let uu____5373 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5373
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5371)
                                 in
                              FStar_Errors.raise_error uu____5365
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5383 =
                                let uu____5386 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5386 u_c
                                 in
                              FStar_All.pipe_right uu____5383 FStar_Util.must
                               in
                            let e2 =
                              let uu____5392 =
                                let uu____5399 =
                                  let uu____5400 =
                                    let uu____5427 =
                                      let uu____5444 =
                                        let uu____5453 =
                                          FStar_Syntax_Syntax.mk_Total' repr
                                            (FStar_Pervasives_Native.Some u_c)
                                           in
                                        FStar_Util.Inr uu____5453  in
                                      (uu____5444,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (e1, uu____5427,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____5400
                                   in
                                FStar_Syntax_Syntax.mk uu____5399  in
                              uu____5392 FStar_Pervasives_Native.None
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5495 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5495
                             then
                               let uu____5499 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5499
                             else ());
                            (let uu____5504 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5504 with
                             | (e3,uu____5518,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5522 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5522
                                   then
                                     let uu____5526 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5528 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5526 uu____5528
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
                                     let uu____5575 =
                                       let uu____5582 =
                                         let uu____5583 =
                                           let uu____5610 =
                                             let uu____5613 =
                                               FStar_All.pipe_right
                                                 expected_c1
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5613
                                               (fun uu____5618  ->
                                                  FStar_Pervasives_Native.Some
                                                    uu____5618)
                                              in
                                           (tm1,
                                             ((FStar_Util.Inr expected_c1),
                                               _tacopt), uu____5610)
                                            in
                                         FStar_Syntax_Syntax.Tm_ascribed
                                           uu____5583
                                          in
                                       FStar_Syntax_Syntax.mk uu____5582  in
                                     uu____5575 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let uu____5655 =
                                     let uu____5662 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5662
                                      in
                                   match uu____5655 with
                                   | (top2,c,g_env) ->
                                       let uu____5672 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5672)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5676) ->
           let uu____5723 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5723 with
            | (env0,uu____5737) ->
                let uu____5742 = tc_comp env0 expected_c  in
                (match uu____5742 with
                 | (expected_c1,uu____5756,g) ->
                     let uu____5758 =
                       let uu____5765 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5765 e1  in
                     (match uu____5758 with
                      | (e2,c',g') ->
                          let uu____5775 =
                            let uu____5786 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5786 with
                            | (c'1,g_c') ->
                                let uu____5803 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5803 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____5823 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____5823))
                             in
                          (match uu____5775 with
                           | (e3,expected_c2,g'') ->
                               let uu____5845 = tc_tactic_opt env0 topt  in
                               (match uu____5845 with
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
                                      let uu____5905 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5905
                                       in
                                    let uu____5906 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5906 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5923 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5923
                                            in
                                         let uu____5924 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5924)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5928) ->
           let uu____5975 = FStar_Syntax_Util.type_u ()  in
           (match uu____5975 with
            | (k,u) ->
                let uu____5988 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____5988 with
                 | (t1,uu____6002,f) ->
                     let uu____6004 = tc_tactic_opt env1 topt  in
                     (match uu____6004 with
                      | (topt1,gtac) ->
                          let uu____6023 =
                            let uu____6030 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6030 e1  in
                          (match uu____6023 with
                           | (e2,c,g) ->
                               let uu____6040 =
                                 let uu____6045 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____6051  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____6045 e2 c f
                                  in
                               (match uu____6040 with
                                | (c1,f1) ->
                                    let uu____6061 =
                                      let uu____6068 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____6068
                                        c1
                                       in
                                    (match uu____6061 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____6115 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____6115
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____6117 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____6117)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6118;
              FStar_Syntax_Syntax.vars = uu____6119;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6198 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6198 with
            | (unary_op,uu____6222) ->
                let head =
                  let uu____6250 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6250
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
              FStar_Syntax_Syntax.pos = uu____6298;
              FStar_Syntax_Syntax.vars = uu____6299;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6378 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6378 with
            | (unary_op,uu____6402) ->
                let head =
                  let uu____6430 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6430
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
                (FStar_Const.Const_reflect uu____6478);
              FStar_Syntax_Syntax.pos = uu____6479;
              FStar_Syntax_Syntax.vars = uu____6480;_},a::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6559 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6559 with
            | (unary_op,uu____6583) ->
                let head =
                  let uu____6611 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____6611
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
              FStar_Syntax_Syntax.pos = uu____6659;
              FStar_Syntax_Syntax.vars = uu____6660;_},a1::a2::hd::rest)
           ->
           let rest1 = hd :: rest  in
           let uu____6756 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6756 with
            | (unary_op,uu____6780) ->
                let head =
                  let uu____6808 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____6808
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
              FStar_Syntax_Syntax.pos = uu____6864;
              FStar_Syntax_Syntax.vars = uu____6865;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6903 =
             let uu____6910 =
               let uu____6911 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6911  in
             tc_term uu____6910 e1  in
           (match uu____6903 with
            | (e2,c,g) ->
                let uu____6935 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6935 with
                 | (head,uu____6959) ->
                     let uu____6984 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7017 =
                       let uu____7018 =
                         let uu____7019 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7019  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7018
                        in
                     (uu____6984, uu____7017, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7020;
              FStar_Syntax_Syntax.vars = uu____7021;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7074 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7074 with
            | (head,uu____7098) ->
                let env' =
                  let uu____7124 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7124  in
                let uu____7125 = tc_term env' r  in
                (match uu____7125 with
                 | (er,uu____7139,gr) ->
                     let uu____7141 = tc_term env1 t  in
                     (match uu____7141 with
                      | (t1,tt,gt) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt  in
                          let uu____7158 =
                            let uu____7159 =
                              let uu____7164 =
                                let uu____7165 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____7174 =
                                  let uu____7185 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____7185]  in
                                uu____7165 :: uu____7174  in
                              FStar_Syntax_Syntax.mk_Tm_app head uu____7164
                               in
                            uu____7159 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7158, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7218;
              FStar_Syntax_Syntax.vars = uu____7219;_},uu____7220)
           ->
           let uu____7245 =
             let uu____7251 =
               let uu____7253 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7253  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7251)  in
           FStar_Errors.raise_error uu____7245 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7263;
              FStar_Syntax_Syntax.vars = uu____7264;_},uu____7265)
           ->
           let uu____7290 =
             let uu____7296 =
               let uu____7298 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7298  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7296)  in
           FStar_Errors.raise_error uu____7290 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7308;
              FStar_Syntax_Syntax.vars = uu____7309;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7356 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7356 with
             | (env0,uu____7370) ->
                 let uu____7375 = tc_term env0 e1  in
                 (match uu____7375 with
                  | (e2,c,g) ->
                      let uu____7391 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7391 with
                       | (reify_op,uu____7415) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7441 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7441 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7456 =
                                    let uu____7458 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7458  in
                                  if uu____7456
                                  then
                                    let uu____7461 =
                                      let uu____7467 =
                                        let uu____7469 =
                                          FStar_Ident.string_of_lid ef  in
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          uu____7469
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7467)
                                       in
                                    FStar_Errors.raise_error uu____7461
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
                                    let uu____7512 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7515 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7515
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7512
                                    then
                                      let uu____7518 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7518
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
                                       let uu____7530 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7530
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7531 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7531 with
                                  | (e4,c3,g') ->
                                      let uu____7547 =
                                        let uu____7548 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7548
                                         in
                                      (e4, c3, uu____7547))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7550;
              FStar_Syntax_Syntax.vars = uu____7551;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7599 =
               let uu____7601 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7601  in
             if uu____7599
             then
               let uu____7604 =
                 let uu____7610 =
                   let uu____7612 = FStar_Ident.string_of_lid l  in
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     uu____7612
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7610)  in
               FStar_Errors.raise_error uu____7604 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7618 = FStar_Syntax_Util.head_and_args top  in
             match uu____7618 with
             | (reflect_op,uu____7642) ->
                 let uu____7667 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7667 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7688 =
                        let uu____7694 =
                          let uu____7696 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7696
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7694)  in
                      FStar_Errors.raise_error uu____7688
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7718 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7718 with
                       | (env_no_ex,uu____7732) ->
                           let uu____7737 =
                             let uu____7746 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7746 with
                             | (e2,c,g) ->
                                 ((let uu____7765 =
                                     let uu____7767 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7767
                                      in
                                   if uu____7765
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7737 with
                            | (e2,c_e,g_e) ->
                                let uu____7805 =
                                  let uu____7820 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____7820 with
                                  | (a,u_a) ->
                                      let uu____7841 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____7841 with
                                       | (a_uvar,uu____7870,g_a) ->
                                           let uu____7884 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____7884, u_a, a_uvar, g_a))
                                   in
                                (match uu____7805 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____7926 =
                                         let uu____7927 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____7927.FStar_Syntax_Syntax.n  in
                                       match uu____7926 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7940,uu____7941::args) ->
                                           args
                                       | uu____7983 ->
                                           let uu____7984 =
                                             let uu____7990 =
                                               let uu____7992 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____7994 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____7996 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____7992 uu____7994
                                                 uu____7996
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____7990)
                                              in
                                           FStar_Errors.raise_error
                                             uu____7984
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8011 =
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
                                       FStar_All.pipe_right uu____8011
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8047 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8047 with
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
                                          let uu____8070 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8070))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8109 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8109 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head,(uu____8159,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____8160))::(tau,FStar_Pervasives_Native.None
                                                               )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8213 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8213 with
            | (head1,args) ->
                tc_synth head1 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8288 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8498 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8288 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8617 =
               let uu____8618 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8618 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8617 instantiate_both  in
           ((let uu____8634 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8634
             then
               let uu____8637 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8639 = FStar_Syntax_Print.term_to_string top  in
               let uu____8641 =
                 let uu____8643 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8643
                   (fun uu___3_8650  ->
                      match uu___3_8650 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8637
                 uu____8639 uu____8641
             else ());
            (let uu____8659 = tc_term (no_inst env2) head  in
             match uu____8659 with
             | (head1,chead,g_head) ->
                 let uu____8675 =
                   let uu____8680 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8680
                     (fun uu____8697  ->
                        match uu____8697 with
                        | (c,g) ->
                            let uu____8708 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8708))
                    in
                 (match uu____8675 with
                  | (chead1,g_head1) ->
                      let uu____8717 =
                        let uu____8724 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8727 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8727))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head1)
                           in
                        if uu____8724
                        then
                          let uu____8736 =
                            let uu____8743 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head1 chead1
                              g_head1 args uu____8743
                             in
                          match uu____8736 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8757 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head1 chead1 g_head1
                             args uu____8757)
                         in
                      (match uu____8717 with
                       | (e1,c,g) ->
                           let uu____8769 =
                             let uu____8776 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8776
                             then
                               let uu____8785 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8785 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8801 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8801, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8769 with
                            | (e2,c1,implicits) ->
                                ((let uu____8814 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8814
                                  then
                                    let uu____8817 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8817
                                  else ());
                                 (let uu____8822 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8822 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8841 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8841
                                        then
                                          let uu____8844 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8846 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8844 uu____8846
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8851 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8874;
                FStar_Syntax_Syntax.lbunivs = uu____8875;
                FStar_Syntax_Syntax.lbtyp = uu____8876;
                FStar_Syntax_Syntax.lbeff = uu____8877;
                FStar_Syntax_Syntax.lbdef = uu____8878;
                FStar_Syntax_Syntax.lbattrs = uu____8879;
                FStar_Syntax_Syntax.lbpos = uu____8880;_}::[]),uu____8881)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____8907),uu____8908) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8926;
                FStar_Syntax_Syntax.lbunivs = uu____8927;
                FStar_Syntax_Syntax.lbtyp = uu____8928;
                FStar_Syntax_Syntax.lbeff = uu____8929;
                FStar_Syntax_Syntax.lbdef = uu____8930;
                FStar_Syntax_Syntax.lbattrs = uu____8931;
                FStar_Syntax_Syntax.lbpos = uu____8932;_}::uu____8933),uu____8934)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____8962),uu____8963) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____8989 =
        let uu____8990 = FStar_Syntax_Subst.compress top  in
        uu____8990.FStar_Syntax_Syntax.n  in
      match uu____8989 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9037 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9037 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9057 = tc_term env11 e1  in
               (match uu____9057 with
                | (e11,c1,g1) ->
                    let uu____9073 =
                      let uu____9084 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9084 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9073 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9139 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9153 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9153 with
                                | (k,uu____9165) ->
                                    let uu____9166 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9166 with
                                     | (res_t,uu____9187,g) ->
                                         let uu____9201 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9202 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9201, res_t, uu____9202)))
                            in
                         (match uu____9139 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9213 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9213
                                then
                                  let uu____9216 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9216
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
                                let uu____9324 =
                                  let uu____9332 =
                                    FStar_List.fold_right
                                      (fun uu____9425  ->
                                         fun uu____9426  ->
                                           match (uu____9425, uu____9426)
                                           with
                                           | ((branch,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable)) ->
                                               let uu____9698 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9698,
                                                 (erasable || erasable_branch)))
                                      t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9332 with
                                  | (cases,g,erasable) ->
                                      let uu____9812 =
                                        FStar_TypeChecker_Util.bind_cases env
                                          res_t cases guard_x
                                         in
                                      (uu____9812, g, erasable)
                                   in
                                match uu____9324 with
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
                                        let uu____9832 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9832
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____9974  ->
                                                  match uu____9974 with
                                                  | ((pat,wopt,br),uu____10022,eff_label,uu____10024,uu____10025,uu____10026,uu____10027)
                                                      ->
                                                      let uu____10066 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10066)))
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
                                      let uu____10133 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10133
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10141 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10141  in
                                         let lb =
                                           let uu____10145 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10145 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10151 =
                                             let uu____10158 =
                                               let uu____10159 =
                                                 let uu____10173 =
                                                   let uu____10176 =
                                                     let uu____10177 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         guard_x
                                                        in
                                                     [uu____10177]  in
                                                   FStar_Syntax_Subst.close
                                                     uu____10176 e_match
                                                    in
                                                 ((false, [lb]), uu____10173)
                                                  in
                                               FStar_Syntax_Syntax.Tm_let
                                                 uu____10159
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10158
                                              in
                                           uu____10151
                                             FStar_Pervasives_Native.None
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10210 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10210
                                      then
                                        let uu____10213 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10215 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10213 uu____10215
                                      else ());
                                     (let uu____10220 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10220)))))))))
      | uu____10221 ->
          let uu____10222 =
            let uu____10224 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10224  in
          failwith uu____10222

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
          let uu____10249 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10288))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10329 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10249 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10362 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10362 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10366 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10366)
                 in
              let uu____10369 =
                let uu____10376 =
                  let uu____10377 =
                    let uu____10378 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10378
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10377  in
                tc_term uu____10376 typ  in
              (match uu____10369 with
               | (typ1,uu____10394,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10397 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10397 with
                     | (tau1,uu____10411,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1324_10416 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1324_10416.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1324_10416.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10418 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10418
                            then
                              let uu____10423 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10423
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10429 =
                              let uu____10430 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10430
                               in
                            (t, uu____10429,
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
            let uu___1334_10436 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1334_10436.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1334_10436.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1334_10436.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1334_10436.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1334_10436.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1334_10436.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1334_10436.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1334_10436.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1334_10436.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1334_10436.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1334_10436.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1334_10436.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1334_10436.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1334_10436.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1334_10436.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1334_10436.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1334_10436.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1334_10436.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1334_10436.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1334_10436.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1334_10436.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1334_10436.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1334_10436.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1334_10436.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1334_10436.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1334_10436.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1334_10436.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1334_10436.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1334_10436.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1334_10436.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1334_10436.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1334_10436.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1334_10436.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1334_10436.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1334_10436.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1334_10436.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1334_10436.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1334_10436.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1334_10436.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1334_10436.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1334_10436.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1334_10436.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1334_10436.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1334_10436.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1334_10436.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____10438 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10438

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
          let uu____10460 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10460 with
           | (tactic1,uu____10474,g) ->
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
        let uu____10527 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t
           in
        match uu____10527 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____10548 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10548
              then FStar_Util.Inl t1
              else
                (let uu____10557 =
                   let uu____10558 = FStar_Syntax_Syntax.mk_Total t1  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10558
                    in
                 FStar_Util.Inr uu____10557)
               in
            let is_data_ctor uu___4_10567 =
              match uu___4_10567 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10572) -> true
              | uu____10580 -> false  in
            let uu____10584 =
              (is_data_ctor dc) &&
                (let uu____10587 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10587)
               in
            if uu____10584
            then
              let uu____10596 =
                let uu____10602 =
                  let uu____10604 =
                    FStar_Ident.string_of_lid v.FStar_Syntax_Syntax.v  in
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    uu____10604
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10602)  in
              let uu____10608 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10596 uu____10608
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10626 =
            let uu____10632 =
              let uu____10634 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10634
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10632)  in
          FStar_Errors.raise_error uu____10626 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10662 =
            let uu____10667 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10667  in
          value_check_expected_typ env1 e uu____10662
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10669 =
            let uu____10682 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10682 with
            | FStar_Pervasives_Native.None  ->
                let uu____10697 = FStar_Syntax_Util.type_u ()  in
                (match uu____10697 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10669 with
           | (t,uu____10735,g0) ->
               let uu____10749 =
                 let uu____10762 =
                   let uu____10764 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____10764
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____10762 r env1 t
                  in
               (match uu____10749 with
                | (e1,uu____10774,g1) ->
                    let uu____10788 =
                      let uu____10789 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10789
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10790 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10788, uu____10790)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10792 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10802 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____10802)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10792 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1400_10816 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1400_10816.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1400_10816.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____10819 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____10819 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____10840 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____10840
                       then FStar_Util.Inl t1
                       else
                         (let uu____10849 =
                            let uu____10850 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10850
                             in
                          FStar_Util.Inr uu____10849)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10852;
             FStar_Syntax_Syntax.vars = uu____10853;_},uu____10854)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10859 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10859
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10869 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10869
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10879;
             FStar_Syntax_Syntax.vars = uu____10880;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____10889 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10889 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10913 =
                     let uu____10919 =
                       let uu____10921 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____10923 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____10925 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10921 uu____10923 uu____10925
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10919)
                      in
                   let uu____10929 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____10913 uu____10929)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10946 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10951 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10951 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_uinst (uu____10952,us) ->
          let uu____10958 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
              "Universe applications are only allowed on top-level identifiers")
            uu____10958
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
                                let uu___1484_11112 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1484_11112.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1484_11112.FStar_Syntax_Syntax.vars)
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
                                      let uu___1522_11290 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1522_11290.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1522_11290.FStar_Syntax_Syntax.vars)
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
                  (let uu___1535_11362 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1535_11362.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1535_11362.FStar_Syntax_Syntax.vars)
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
            let uu____11614 =
              let uu____11619 =
                let uu____11620 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____11620 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head1 uu____11619  in
            uu____11614 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11637 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____11637 with
           | (tc1,uu____11651,f) ->
               let uu____11653 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11653 with
                | (head2,args) ->
                    let comp_univs =
                      let uu____11703 =
                        let uu____11704 = FStar_Syntax_Subst.compress head2
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
                                       (let uu___1664_11999 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1664_11999.FStar_Syntax_Syntax.effect_name);
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
          let fail msg t =
            let uu____12093 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____12093 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____12182 bs2 bs_expected1 =
              match uu____12182 with
              | (env2,subst) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst)
                   | ((uu____12289,FStar_Pervasives_Native.None )::uu____12290,
                      (hd_e,q)::uu____12293) when
                       FStar_Syntax_Syntax.is_implicit_or_meta q ->
                       let bv =
                         let uu____12345 =
                           let uu____12348 =
                             FStar_Ident.range_of_id
                               hd_e.FStar_Syntax_Syntax.ppname
                              in
                           FStar_Pervasives_Native.Some uu____12348  in
                         let uu____12349 =
                           FStar_Syntax_Subst.subst subst
                             hd_e.FStar_Syntax_Syntax.sort
                            in
                         FStar_Syntax_Syntax.new_bv uu____12345 uu____12349
                          in
                       aux (env2, subst) ((bv, q) :: bs2) bs_expected1
                   | ((hd,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta
                              uu____12444),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12445)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____12460),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12461)) -> true
                           | uu____12470 -> false  in
                         let uu____12480 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____12483 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____12483 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____12480
                         then
                           let uu____12485 =
                             let uu____12491 =
                               let uu____12493 =
                                 FStar_Syntax_Print.bv_to_string hd  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____12493
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____12491)
                              in
                           let uu____12497 =
                             FStar_Syntax_Syntax.range_of_bv hd  in
                           FStar_Errors.raise_error uu____12485 uu____12497
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____12501 =
                           let uu____12508 =
                             let uu____12509 =
                               FStar_Syntax_Util.unmeta
                                 hd.FStar_Syntax_Syntax.sort
                                in
                             uu____12509.FStar_Syntax_Syntax.n  in
                           match uu____12508 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12520 ->
                               ((let uu____12522 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____12522
                                 then
                                   let uu____12525 =
                                     FStar_Syntax_Print.bv_to_string hd  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____12525
                                 else ());
                                (let uu____12530 =
                                   tc_tot_or_gtot_term env2
                                     hd.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____12530 with
                                 | (t,uu____12544,g1_env) ->
                                     let g2_env =
                                       let uu____12547 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       match uu____12547 with
                                       | FStar_Pervasives_Native.Some g ->
                                           FStar_All.pipe_right g
                                             (FStar_TypeChecker_Rel.resolve_implicits
                                                env2)
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____12551 =
                                             FStar_TypeChecker_Rel.get_subtyping_prop
                                               env2 expected_t t
                                              in
                                           (match uu____12551 with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____12554 =
                                                  FStar_TypeChecker_Err.basic_type_error
                                                    env2
                                                    FStar_Pervasives_Native.None
                                                    expected_t t
                                                   in
                                                let uu____12560 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____12554 uu____12560
                                            | FStar_Pervasives_Native.Some
                                                g_env ->
                                                FStar_TypeChecker_Util.label_guard
                                                  (hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                  "Type annotation on parameter incompatible with the expected type"
                                                  g_env)
                                        in
                                     let uu____12563 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____12563)))
                            in
                         match uu____12501 with
                         | (t,g_env) ->
                             let hd1 =
                               let uu___1776_12589 = hd  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1776_12589.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1776_12589.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd1, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst1 =
                               let uu____12612 =
                                 FStar_Syntax_Syntax.bv_to_name hd1  in
                               maybe_extend_subst subst b_expected
                                 uu____12612
                                in
                             let uu____12615 =
                               aux (env_b, subst1) bs3 bs_expected2  in
                             (match uu____12615 with
                              | (env_bs,bs4,rest,g'_env_b,subst2) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____12680 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____12680,
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
                  | uu____12852 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____12862 = tc_binders env1 bs  in
                  match uu____12862 with
                  | (bs1,envbody,g_env,uu____12892) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____12938 =
                    let uu____12939 = FStar_Syntax_Subst.compress t2  in
                    uu____12939.FStar_Syntax_Syntax.n  in
                  match uu____12938 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____12962 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12982 -> failwith "Impossible");
                       (let uu____12992 = tc_binders env1 bs  in
                        match uu____12992 with
                        | (bs1,envbody,g_env,uu____13024) ->
                            let uu____13025 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13025 with
                             | (envbody1,uu____13053) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____13064;
                         FStar_Syntax_Syntax.pos = uu____13065;
                         FStar_Syntax_Syntax.vars = uu____13066;_},uu____13067)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____13111 -> failwith "Impossible");
                       (let uu____13121 = tc_binders env1 bs  in
                        match uu____13121 with
                        | (bs1,envbody,g_env,uu____13153) ->
                            let uu____13154 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13154 with
                             | (envbody1,uu____13182) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____13194) ->
                      let uu____13199 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____13199 with
                       | (uu____13240,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____13287 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____13287 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____13422 c_expected2
                               body3 =
                               match uu____13422 with
                               | (env_bs,bs2,more,guard_env,subst) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____13536 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____13536,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____13553 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____13553
                                           in
                                        let uu____13554 =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c
                                           in
                                        (env_bs, bs2, guard_env, uu____13554,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp subst
                                            c_expected2
                                           in
                                        let uu____13571 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____13571
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
                                               let uu____13637 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____13637 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____13664 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____13664 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst1)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____13719 =
                                                           let uu____13746 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____13746,
                                                             subst1)
                                                            in
                                                         handle_more
                                                           uu____13719
                                                           c_expected4 body3))
                                           | uu____13769 ->
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
                             let uu____13798 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____13798 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1902_13863 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1902_13863.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1902_13863.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1902_13863.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1902_13863.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1902_13863.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1902_13863.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1902_13863.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1902_13863.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1902_13863.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1902_13863.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1902_13863.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1902_13863.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1902_13863.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1902_13863.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1902_13863.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1902_13863.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___1902_13863.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1902_13863.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1902_13863.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1902_13863.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1902_13863.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1902_13863.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1902_13863.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1902_13863.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1902_13863.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1902_13863.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1902_13863.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1902_13863.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1902_13863.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1902_13863.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1902_13863.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1902_13863.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1902_13863.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1902_13863.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1902_13863.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___1902_13863.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1902_13863.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___1902_13863.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1902_13863.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1902_13863.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1902_13863.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1902_13863.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1902_13863.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1902_13863.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___1902_13863.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             let uu____13870 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____13936  ->
                                       fun uu____13937  ->
                                         match (uu____13936, uu____13937)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____14028 =
                                               let uu____14035 =
                                                 let uu____14036 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____14036
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____14035 t3  in
                                             (match uu____14028 with
                                              | (t4,uu____14060,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____14073 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1920_14076
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1920_14076.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1920_14076.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____14073 ::
                                                          letrec_binders
                                                    | uu____14077 ->
                                                        letrec_binders
                                                     in
                                                  let uu____14082 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____14082)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____13870 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____14102 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____14102)
                              in
                           let uu____14105 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____14105 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____14141 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____14141 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____14178 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____14178))))
                  | uu____14185 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____14207 =
                          let uu____14208 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____14208
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____14207
                      else
                        (let uu____14212 =
                           expected_function_typ env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____14212 with
                         | (uu____14251,bs1,uu____14253,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14275 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14275 with
          | (env1,topt) ->
              ((let uu____14295 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14295
                then
                  let uu____14298 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14298
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14312 = expected_function_typ env1 topt body  in
                match uu____14312 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14353 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14353
                      then
                        let uu____14356 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14361 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14366 =
                          let uu____14368 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14368 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14356 uu____14361 uu____14366
                      else ());
                     (let uu____14378 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14378
                      then
                        let uu____14383 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14386 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14383 uu____14386
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14392 =
                        let should_check_expected_effect =
                          let uu____14405 =
                            let uu____14412 =
                              let uu____14413 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____14413.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____14412)  in
                          match uu____14405 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____14419,(FStar_Util.Inr
                                           expected_c,uu____14421),uu____14422))
                              -> false
                          | uu____14472 -> true  in
                        let uu____14480 =
                          tc_term
                            (let uu___1993_14489 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1993_14489.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1993_14489.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1993_14489.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1993_14489.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1993_14489.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1993_14489.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1993_14489.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1993_14489.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1993_14489.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1993_14489.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1993_14489.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1993_14489.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1993_14489.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1993_14489.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1993_14489.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (uu___1993_14489.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1993_14489.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1993_14489.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1993_14489.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1993_14489.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1993_14489.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1993_14489.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1993_14489.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1993_14489.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1993_14489.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1993_14489.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1993_14489.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1993_14489.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1993_14489.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1993_14489.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1993_14489.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1993_14489.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1993_14489.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1993_14489.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1993_14489.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1993_14489.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1993_14489.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1993_14489.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1993_14489.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1993_14489.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1993_14489.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1993_14489.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1993_14489.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1993_14489.FStar_TypeChecker_Env.erasable_types_tab)
                             }) body1
                           in
                        match uu____14480 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____14516 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____14516 with
                               | (cbody1,g_lc) ->
                                   let uu____14533 =
                                     check_expected_effect
                                       (let uu___2004_14542 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___2004_14542.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___2004_14542.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___2004_14542.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___2004_14542.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___2004_14542.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___2004_14542.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___2004_14542.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___2004_14542.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___2004_14542.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___2004_14542.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___2004_14542.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___2004_14542.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___2004_14542.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___2004_14542.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___2004_14542.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___2004_14542.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___2004_14542.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___2004_14542.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___2004_14542.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___2004_14542.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___2004_14542.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___2004_14542.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___2004_14542.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___2004_14542.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___2004_14542.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___2004_14542.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___2004_14542.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___2004_14542.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___2004_14542.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___2004_14542.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___2004_14542.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___2004_14542.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____14533 with
                                    | (body3,cbody2,guard) ->
                                        let uu____14556 =
                                          let uu____14557 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____14557
                                           in
                                        (body3, cbody2, uu____14556)))
                            else
                              (let uu____14564 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____14564 with
                               | (cbody1,g_lc) ->
                                   let uu____14581 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____14581))
                         in
                      match uu____14392 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14604 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14607 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14607)
                               in
                            if uu____14604
                            then
                              let uu____14610 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14611 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14610
                                uu____14611
                            else
                              (let guard =
                                 let uu____14615 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14615
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
                          let uu____14630 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14654
                                     -> (e, t_annot, guard1)
                                 | uu____14669 ->
                                     let lc =
                                       let uu____14671 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____14671
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____14672 =
                                       FStar_TypeChecker_Util.check_has_type
                                         env1 e lc t1
                                        in
                                     (match uu____14672 with
                                      | (e1,uu____14686,guard') ->
                                          let uu____14688 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____14688)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____14630 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____14699 =
                                 let uu____14704 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14704 guard2
                                  in
                               (match uu____14699 with
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
              (let uu____14755 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____14755
               then
                 let uu____14758 =
                   FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos
                    in
                 let uu____14760 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14758
                   uu____14760
               else ());
              (let monadic_application uu____14842 subst arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14842 with
                 | (head1,chead1,ghead1,cres) ->
                     let uu____14911 =
                       check_no_escape (FStar_Pervasives_Native.Some head1)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____14911 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____14925 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14941 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14941
                                   in
                                (cres1, g)
                            | uu____14942 ->
                                let g =
                                  let uu____14952 =
                                    let uu____14953 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____14953
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14952
                                   in
                                let uu____14954 =
                                  let uu____14955 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____14955
                                   in
                                (uu____14954, g)
                             in
                          (match uu____14925 with
                           | (cres2,guard1) ->
                               ((let uu____14965 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____14965
                                 then
                                   let uu____14968 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14968
                                 else ());
                                (let uu____14973 =
                                   let uu____14978 =
                                     let uu____14979 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____14979
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____14980 =
                                     let uu____14981 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____14981
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____14978, uu____14980)  in
                                 match uu____14973 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15005  ->
                                                 match uu____15005 with
                                                 | (uu____15015,uu____15016,lc)
                                                     ->
                                                     (let uu____15024 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15024)
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
                                       let uu____15037 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15037
                                       then
                                         ((let uu____15041 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15041
                                           then
                                             let uu____15044 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15044
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15052 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15052
                                           then
                                             let uu____15055 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15055
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15086  ->
                                              match uu____15086 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15128 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15128
                                                    then
                                                      let uu____15131 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15136 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15138 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15131
                                                        uu____15136
                                                        uu____15138
                                                    else ());
                                                   (let uu____15143 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15143
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
                                       (let uu____15154 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15154
                                        then
                                          let uu____15157 =
                                            FStar_Syntax_Print.term_to_string
                                              head1
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15157
                                        else ());
                                       (let uu____15162 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15162
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
                                       let uu____15173 =
                                         let uu____15174 =
                                           FStar_Syntax_Subst.compress head1
                                            in
                                         uu____15174.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15173 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15179 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15202  ->
                                                  match uu____15202 with
                                                  | (arg,uu____15216,uu____15217)
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
                                         (let uu____15228 =
                                            let map_fun uu____15294 =
                                              match uu____15294 with
                                              | ((e,q),uu____15335,c) ->
                                                  ((let uu____15358 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15358
                                                    then
                                                      let uu____15361 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15363 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15361
                                                        uu____15363
                                                    else ());
                                                   (let uu____15368 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15368
                                                    then
                                                      ((let uu____15394 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15394
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
                                                           (let uu____15435 =
                                                              let uu____15437
                                                                =
                                                                let uu____15438
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head1
                                                                   in
                                                                uu____15438.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15437
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15443
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15443
                                                              | uu____15445
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15435)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15449 =
                                                            let uu____15455 =
                                                              let uu____15457
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15459
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  c.FStar_TypeChecker_Common.eff_name
                                                                 in
                                                              let uu____15461
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15457
                                                                uu____15459
                                                                uu____15461
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15455)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15449)
                                                       else ();
                                                       (let uu____15468 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15468
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
                                                        let uu____15476 =
                                                          let uu____15485 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15485, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15476)))))
                                               in
                                            let uu____15514 =
                                              let uu____15545 =
                                                let uu____15574 =
                                                  let uu____15585 =
                                                    let uu____15594 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head1
                                                       in
                                                    (uu____15594,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15585 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15574
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15545
                                               in
                                            match uu____15514 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____15795 =
                                                  let uu____15796 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15796
                                                   in
                                                let uu____15817 =
                                                  let uu____15818 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____15818
                                                   in
                                                (lifted_args, uu____15795,
                                                  uu____15817)
                                             in
                                          match uu____15228 with
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
                                                uu___6_15929 =
                                                match uu___6_15929 with
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
                                                      let uu____15990 =
                                                        let uu____15997 =
                                                          let uu____15998 =
                                                            let uu____16012 =
                                                              let uu____16015
                                                                =
                                                                let uu____16016
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____16016]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____16015 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____16012)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____15998
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____15997
                                                         in
                                                      uu____15990
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
                                     let uu____16068 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____16068 with
                                      | (comp2,g) ->
                                          ((let uu____16086 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16086
                                            then
                                              let uu____16089 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16091 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16089 uu____16091
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16172 bs args1 =
                 match uu____16172 with
                 | (subst,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16311))::rest,
                         (uu____16313,FStar_Pervasives_Native.None )::uu____16314)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16375 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head) env fvs t
                             in
                          (match uu____16375 with
                           | (t1,g_ex) ->
                               let uu____16388 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____16388 with
                                | (varg,uu____16409,implicits) ->
                                    let subst1 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst  in
                                    let arg =
                                      let uu____16437 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16437)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16446 =
                                      let uu____16481 =
                                        let uu____16492 =
                                          let uu____16501 =
                                            let uu____16502 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____16502
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16501)
                                           in
                                        uu____16492 :: outargs  in
                                      (subst1, uu____16481, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16446 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____16548,FStar_Pervasives_Native.None
                                                                 )::uu____16549)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst tau  in
                          let uu____16611 =
                            tc_tactic FStar_Syntax_Syntax.t_unit
                              FStar_Syntax_Syntax.t_unit env tau1
                             in
                          (match uu____16611 with
                           | (tau2,uu____16625,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16628 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head) env
                                   fvs t
                                  in
                               (match uu____16628 with
                                | (t1,g_ex) ->
                                    let uu____16641 =
                                      let uu____16654 =
                                        let uu____16661 =
                                          let uu____16666 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____16666, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____16661
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____16654
                                       in
                                    (match uu____16641 with
                                     | (varg,uu____16679,implicits) ->
                                         let subst1 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst  in
                                         let arg =
                                           let uu____16707 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____16707)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____16716 =
                                           let uu____16751 =
                                             let uu____16762 =
                                               let uu____16771 =
                                                 let uu____16772 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____16772
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16771)
                                                in
                                             uu____16762 :: outargs  in
                                           (subst1, uu____16751, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____16716 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16888,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16889)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____16900),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16901)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____16909),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16910)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____16925 ->
                                let uu____16934 =
                                  let uu____16940 =
                                    let uu____16942 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____16944 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____16946 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____16948 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16942 uu____16944 uu____16946
                                      uu____16948
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16940)
                                   in
                                FStar_Errors.raise_error uu____16934
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst aqual  in
                            let x1 =
                              let uu___2283_16955 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2283_16955.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2283_16955.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____16957 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____16957
                             then
                               let uu____16960 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____16962 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16964 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16966 =
                                 FStar_Syntax_Print.subst_to_string subst  in
                               let uu____16968 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16960 uu____16962 uu____16964
                                 uu____16966 uu____16968
                             else ());
                            (let uu____16973 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head) env fvs
                                 targ
                                in
                             match uu____16973 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2292_16988 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2292_16988.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2292_16988.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2292_16988.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2292_16988.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2292_16988.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2292_16988.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2292_16988.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2292_16988.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2292_16988.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2292_16988.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2292_16988.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2292_16988.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2292_16988.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2292_16988.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2292_16988.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2292_16988.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___2292_16988.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2292_16988.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2292_16988.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2292_16988.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2292_16988.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2292_16988.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2292_16988.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2292_16988.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2292_16988.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2292_16988.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2292_16988.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2292_16988.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2292_16988.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2292_16988.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2292_16988.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2292_16988.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2292_16988.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2292_16988.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2292_16988.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2292_16988.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2292_16988.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2292_16988.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2292_16988.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2292_16988.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2292_16988.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2292_16988.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2292_16988.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2292_16988.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2292_16988.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____16990 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____16990
                                   then
                                     let uu____16993 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____16995 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____16997 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     let uu____16999 =
                                       FStar_Util.string_of_bool
                                         env2.FStar_TypeChecker_Env.use_eq
                                        in
                                     FStar_Util.print4
                                       "Checking arg (%s) %s at type %s with use_eq:%s\n"
                                       uu____16993 uu____16995 uu____16997
                                       uu____16999
                                   else ());
                                  (let uu____17004 = tc_term env2 e  in
                                   match uu____17004 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17021 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17021
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17044 =
                                           let uu____17047 =
                                             let uu____17056 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17056
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17047
                                            in
                                         (uu____17044, aq)  in
                                       let uu____17065 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17065
                                       then
                                         let subst1 =
                                           let uu____17075 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst
                                             uu____17075 e1
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
                      | (uu____17174,[]) ->
                          monadic_application head_info subst outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17210) ->
                          let uu____17261 =
                            monadic_application head_info subst outargs
                              arg_rets g fvs []
                             in
                          (match uu____17261 with
                           | (head1,chead1,ghead1) ->
                               let uu____17283 =
                                 let uu____17288 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____17288
                                   (fun uu____17305  ->
                                      match uu____17305 with
                                      | (c,g1) ->
                                          let uu____17316 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____17316))
                                  in
                               (match uu____17283 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17359 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____17359
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____17390 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____17390 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head1, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____17413 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____17413
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
                                      | uu____17460 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17468 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____17468
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____17469 =
                                              let uu____17470 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____17470.FStar_Syntax_Syntax.n
                                               in
                                            match uu____17469 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17473;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17474;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____17476)
                                                -> norm_tres tres4
                                            | uu____17484 -> tres3  in
                                          let uu____17485 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____17485
                                      | uu____17487 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____17490 ->
                                          let uu____17491 =
                                            let uu____17497 =
                                              let uu____17499 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____17501 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____17503 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17499 uu____17501
                                                uu____17503
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17497)
                                             in
                                          let uu____17507 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____17491 uu____17507
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____17537 =
                   let uu____17538 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____17538.FStar_Syntax_Syntax.n  in
                 match uu____17537 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17547 ->
                     let uu____17560 =
                       FStar_List.fold_right
                         (fun uu____17591  ->
                            fun uu____17592  ->
                              match uu____17592 with
                              | (bs,guard1) ->
                                  let uu____17619 =
                                    let uu____17632 =
                                      let uu____17633 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17633
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17632
                                     in
                                  (match uu____17619 with
                                   | (t,uu____17650,g) ->
                                       let uu____17664 =
                                         let uu____17667 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17667 :: bs  in
                                       let uu____17668 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17664, uu____17668))) args
                         ([], guard)
                        in
                     (match uu____17560 with
                      | (bs,guard1) ->
                          let uu____17685 =
                            let uu____17692 =
                              let uu____17705 =
                                let uu____17706 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17706
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17705
                               in
                            match uu____17692 with
                            | (t,uu____17723,g) ->
                                let uu____17737 = FStar_Options.ml_ish ()  in
                                if uu____17737
                                then
                                  let uu____17746 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17749 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17746, uu____17749)
                                else
                                  (let uu____17754 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17757 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17754, uu____17757))
                             in
                          (match uu____17685 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17776 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17776
                                 then
                                   let uu____17780 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____17782 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17784 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17780 uu____17782 uu____17784
                                 else ());
                                (let g =
                                   let uu____17790 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17790
                                    in
                                 let uu____17791 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17791))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17792;
                        FStar_Syntax_Syntax.pos = uu____17793;
                        FStar_Syntax_Syntax.vars = uu____17794;_},uu____17795)
                     ->
                     let uu____17832 =
                       FStar_List.fold_right
                         (fun uu____17863  ->
                            fun uu____17864  ->
                              match uu____17864 with
                              | (bs,guard1) ->
                                  let uu____17891 =
                                    let uu____17904 =
                                      let uu____17905 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17905
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17904
                                     in
                                  (match uu____17891 with
                                   | (t,uu____17922,g) ->
                                       let uu____17936 =
                                         let uu____17939 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17939 :: bs  in
                                       let uu____17940 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17936, uu____17940))) args
                         ([], guard)
                        in
                     (match uu____17832 with
                      | (bs,guard1) ->
                          let uu____17957 =
                            let uu____17964 =
                              let uu____17977 =
                                let uu____17978 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17978
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17977
                               in
                            match uu____17964 with
                            | (t,uu____17995,g) ->
                                let uu____18009 = FStar_Options.ml_ish ()  in
                                if uu____18009
                                then
                                  let uu____18018 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18021 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18018, uu____18021)
                                else
                                  (let uu____18026 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18029 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18026, uu____18029))
                             in
                          (match uu____17957 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18048 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18048
                                 then
                                   let uu____18052 =
                                     FStar_Syntax_Print.term_to_string head
                                      in
                                   let uu____18054 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18056 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18052 uu____18054 uu____18056
                                 else ());
                                (let g =
                                   let uu____18062 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18062
                                    in
                                 let uu____18063 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18063))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18086 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18086 with
                      | (bs1,c1) ->
                          let head_info = (head, chead, ghead, c1)  in
                          ((let uu____18109 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18109
                            then
                              let uu____18112 =
                                FStar_Syntax_Print.term_to_string head  in
                              let uu____18114 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18116 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18119 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18112 uu____18114 uu____18116
                                uu____18119
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18165) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18171,uu____18172) ->
                     check_function_app t guard
                 | uu____18213 ->
                     let uu____18214 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18214
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
                  let uu____18297 =
                    FStar_List.fold_left2
                      (fun uu____18366  ->
                         fun uu____18367  ->
                           fun uu____18368  ->
                             match (uu____18366, uu____18367, uu____18368)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____18521 =
                                     let uu____18523 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____18523 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____18521
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18529 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____18529 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head seen
                                          in
                                       let g1 =
                                         let uu____18558 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18558 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18563 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____18563)
                                              &&
                                              (let uu____18566 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____18566))
                                          in
                                       let uu____18568 =
                                         let uu____18579 =
                                           let uu____18590 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____18590]  in
                                         FStar_List.append seen uu____18579
                                          in
                                       let uu____18623 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____18568, uu____18623, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____18297 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____18691 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____18691
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____18694 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____18694 with | (c2,g) -> (e, c2, g)))
              | uu____18711 ->
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
            let uu____18809 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18809 with
            | (head,args) ->
                let uu____18852 =
                  let uu____18853 = FStar_Syntax_Subst.compress head  in
                  uu____18853.FStar_Syntax_Syntax.n  in
                (match uu____18852 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18857;
                        FStar_Syntax_Syntax.vars = uu____18858;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18865 ->
                     if norm1
                     then t1
                     else
                       (let uu____18869 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____18869))
          
          and unfold_once t f us args =
            let uu____18887 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____18887
            then t
            else
              (let uu____18892 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____18892 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18912 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____18912 with
                    | (uu____18917,head_def) ->
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
          let uu____18924 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____18924  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18943 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____18943
           then
             let uu____18948 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____18950 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18948 uu____18950
           else ());
          (let fail1 msg =
             let msg1 =
               let uu____18970 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____18972 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18970 uu____18972 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____18976 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____18976 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19020 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19020 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19021;
                    FStar_Syntax_Syntax.pos = uu____19022;
                    FStar_Syntax_Syntax.vars = uu____19023;_} ->
                    let uu____19026 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19026 with
                     | (head_p,args_p) ->
                         let uu____19069 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19069
                         then
                           let uu____19072 =
                             let uu____19073 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19073.FStar_Syntax_Syntax.n  in
                           (match uu____19072 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19078 =
                                    let uu____19080 =
                                      let uu____19082 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19082
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19080
                                     in
                                  if uu____19078
                                  then
                                    fail1
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail1 ""
                                 else ();
                                 (let uu____19110 =
                                    let uu____19135 =
                                      let uu____19139 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19139
                                       in
                                    match uu____19135 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n ->
                                        let uu____19188 =
                                          FStar_Util.first_N n args_p  in
                                        (match uu____19188 with
                                         | (params_p,uu____19246) ->
                                             let uu____19287 =
                                               FStar_Util.first_N n args_s
                                                in
                                             (match uu____19287 with
                                              | (params_s,uu____19345) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19110 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____19474  ->
                                             fun uu____19475  ->
                                               match (uu____19474,
                                                       uu____19475)
                                               with
                                               | ((p,uu____19509),(s,uu____19511))
                                                   ->
                                                   let uu____19544 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____19544 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____19547 =
                                                          let uu____19549 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____19551 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19549
                                                            uu____19551
                                                           in
                                                        fail1 uu____19547
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
                            | uu____19556 ->
                                fail1 "Pattern matching a non-inductive type")
                         else
                           (let uu____19560 =
                              let uu____19562 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____19564 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19562 uu____19564
                               in
                            fail1 uu____19560))
                | uu____19567 ->
                    let uu____19568 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____19568 with
                     | FStar_Pervasives_Native.None  -> fail1 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____19611 = FStar_Syntax_Util.head_and_args e  in
          match uu____19611 with
          | (head,args) ->
              (match head.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19681 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____19681 with
                    | (us,t_f) ->
                        let uu____19701 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____19701 with
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
                              (let rec aux uu____19814 formals1 args1 =
                                 match uu____19814 with
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
                                          let uu____19965 =
                                            FStar_Syntax_Subst.subst subst t
                                             in
                                          (pat_e, uu____19965, bvs, guard,
                                            erasable)
                                      | ((f1,uu____19972)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____20030 =
                                            let uu____20051 =
                                              let uu____20052 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____20052.FStar_Syntax_Syntax.n
                                               in
                                            match uu____20051 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2599_20077 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2599_20077.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2599_20077.FStar_Syntax_Syntax.index);
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
                                                uu____20100 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____20114 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____20114 with
                                                 | (a1,uu____20142,g) ->
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
                                            | uu____20166 ->
                                                fail "Not a simple pattern"
                                             in
                                          (match uu____20030 with
                                           | (a1,subst1,bvs1,g) ->
                                               let uu____20231 =
                                                 let uu____20254 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst1,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20254)
                                                  in
                                               aux uu____20231 formals2 args2)
                                      | uu____20293 ->
                                          fail "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20352 -> fail "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____20418 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____20418
           then
             let uu____20423 = FStar_Syntax_Print.pat_to_string p  in
             let uu____20425 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20423
               uu____20425
           else ());
          (let id =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20450 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____20450 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____20461 =
                 let uu____20466 =
                   let uu____20467 =
                     let uu____20476 =
                       let uu____20477 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____20477
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____20476
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____20467]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____20466  in
               uu____20461 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____20513 =
                 let uu____20518 =
                   let uu____20519 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____20519]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20518  in
               uu____20513 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20581 ->
               let uu____20588 =
                 let uu____20590 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20590
                  in
               failwith uu____20588
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2638_20612 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2638_20612.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2638_20612.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20613 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____20613,
                 (let uu___2641_20620 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2641_20620.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2645_20624 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2645_20624.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2645_20624.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20625 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id], uu____20625,
                 (let uu___2648_20632 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2648_20632.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____20634 ->
               let uu____20635 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____20635 with
                | (uu____20664,e_c,uu____20666,uu____20667) ->
                    let uu____20672 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____20672 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____20702 =
                              let uu____20704 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____20704  in
                            if uu____20702
                            then
                              let uu____20707 =
                                let uu____20709 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____20711 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20709 uu____20711
                                 in
                              fail uu____20707
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20773  ->
                        match uu____20773 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20803
                                 -> (p1, b)
                             | uu____20813 ->
                                 let uu____20814 =
                                   let uu____20817 =
                                     let uu____20818 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____20818
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____20817
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____20814, b))) sub_pats
                    in
                 let uu___2676_20822 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2676_20822.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20867  ->
                         match uu____20867 with
                         | (x,uu____20877) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20885
                                  -> false
                              | uu____20893 -> true)))
                  in
               let uu____20895 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____20895 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20939 =
                          let uu____20941 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____20943 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____20945 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____20952 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20941 uu____20943 uu____20945 uu____20952
                           in
                        failwith uu____20939)
                     else ();
                     (let uu____20957 =
                        let uu____20969 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____20969 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable)
                            ->
                            let g' =
                              let uu____21006 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21006  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21009 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21009
                              then
                                let uu____21014 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21016 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21018 =
                                  let uu____21020 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21028 =
                                           let uu____21030 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21032 =
                                             let uu____21034 =
                                               let uu____21036 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21036 ")"
                                                in
                                             Prims.op_Hat " : " uu____21034
                                              in
                                           Prims.op_Hat uu____21030
                                             uu____21032
                                            in
                                         Prims.op_Hat "(" uu____21028)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21020
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21014 uu____21016 uu____21018
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable))
                         in
                      match uu____20957 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable) ->
                          let uu____21079 =
                            let uu____21111 =
                              let uu____21143 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21143, erasable,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21225  ->
                                 fun uu____21226  ->
                                   fun x  ->
                                     match (uu____21225, uu____21226) with
                                     | ((env2,bvs,tms,pats,subst,g,erasable1,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____21410 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____21410 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21480 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21480 i
                                                   in
                                                let uu____21481 =
                                                  let uu____21490 =
                                                    let uu____21495 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____21495  in
                                                  FStar_List.map uu____21490
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____21481
                                                 in
                                              let uu____21501 =
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
                                                uu____21501,
                                                (erasable1 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21111 sub_pats1 simple_bvs1
                             in
                          (match uu____21079 with
                           | (_env,bvs,tms,checked_sub_pats,subst,g,erasable1,uu____21560)
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
                                              let uu___2760_21736 = hd  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2760_21736.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____21741 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd1, b) :: uu____21741
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd1,uu____21785)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21822 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd1, b) :: uu____21822
                                             | uu____21842 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21868 ->
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
                                     let uu___2781_21911 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2781_21911.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21923 -> failwith "Impossible"  in
                               let uu____21927 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____21927, g, erasable1))))))
           in
        (let uu____21934 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____21934
         then
           let uu____21939 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21939
         else ());
        (let uu____21944 =
           let uu____21962 =
             let uu___2786_21963 =
               let uu____21964 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____21964 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2786_21963.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2786_21963.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2786_21963.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2786_21963.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2786_21963.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2786_21963.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2786_21963.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2786_21963.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2786_21963.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2786_21963.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2786_21963.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2786_21963.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2786_21963.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2786_21963.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2786_21963.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2786_21963.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___2786_21963.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2786_21963.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2786_21963.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2786_21963.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2786_21963.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2786_21963.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2786_21963.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2786_21963.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2786_21963.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2786_21963.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2786_21963.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2786_21963.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2786_21963.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2786_21963.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2786_21963.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2786_21963.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2786_21963.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2786_21963.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2786_21963.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2786_21963.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2786_21963.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2786_21963.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2786_21963.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2786_21963.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2786_21963.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2786_21963.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2786_21963.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2786_21963.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2786_21963.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____21980 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____21962 uu____21980 pat_t  in
         match uu____21944 with
         | (bvs,tms,pat_e,pat,g,erasable) ->
             ((let uu____22019 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22019
               then
                 let uu____22024 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22026 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22024
                   uu____22026
               else ());
              (let uu____22031 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22032 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22031, pat_e, uu____22032, g, erasable))))

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
        let uu____22070 = FStar_Syntax_Subst.open_branch branch  in
        match uu____22070 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22119 = branch  in
            (match uu____22119 with
             | (cpat,uu____22150,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22172 =
                   let uu____22179 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22179
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22172 with
                  | (scrutinee_env,uu____22216) ->
                      let uu____22221 = tc_pat env pat_t pattern  in
                      (match uu____22221 with
                       | (pattern1,pat_bvs,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable)
                           ->
                           ((let uu____22291 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____22291
                             then
                               let uu____22295 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____22297 =
                                 FStar_Syntax_Print.bvs_to_string ";" pat_bvs
                                  in
                               let uu____22300 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____22309 =
                                          let uu____22311 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____22311  in
                                        Prims.op_Hat s uu____22309) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____22295 uu____22297 uu____22300
                             else ());
                            (let uu____22318 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____22348 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____22348
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____22371 =
                                        let uu____22378 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____22378 e  in
                                      match uu____22371 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____22318 with
                             | (when_clause1,g_when) ->
                                 let uu____22435 = tc_term pat_env branch_exp
                                    in
                                 (match uu____22435 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____22494 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun uu____22505  ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____22505) uu____22494
                                           in
                                        let branch_guard =
                                          let uu____22509 =
                                            let uu____22511 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____22511  in
                                          if uu____22509
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22567 =
                                                   let uu____22575 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22575
                                                    in
                                                 match uu____22567 with
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
                                                       let uu____22591 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____22591
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____22612 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____22628
                                                                =
                                                                let uu____22633
                                                                  =
                                                                  let uu____22634
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                  [uu____22634]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc
                                                                  uu____22633
                                                                 in
                                                              uu____22628
                                                                FStar_Pervasives_Native.None
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____22659 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____22659])
                                                     else []
                                                  in
                                               let fail uu____22667 =
                                                 let uu____22668 =
                                                   let uu____22670 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____22672 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____22674 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22670 uu____22672
                                                     uu____22674
                                                    in
                                                 failwith uu____22668  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____22689) ->
                                                     head_constructor t1
                                                 | uu____22694 -> fail ()  in
                                               let force_scrutinee
                                                 uu____22700 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____22701 =
                                                       let uu____22703 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____22705 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22703
                                                         uu____22705
                                                        in
                                                     failwith uu____22701
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____22712 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____22712
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22717,FStar_Syntax_Syntax.Tm_name
                                                  uu____22718) -> []
                                               | (uu____22719,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22722 =
                                                     let uu____22723 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____22724 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____22723
                                                       uu____22724 pat_exp2
                                                      in
                                                   [uu____22722]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22725,FStar_Pervasives_Native.Some
                                                   uu____22726)),uu____22727)
                                                   ->
                                                   let uu____22744 =
                                                     let uu____22751 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____22751 with
                                                     | (env1,uu____22765) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____22744 with
                                                    | (uu____22772,t,uu____22774)
                                                        ->
                                                        let uu____22775 =
                                                          let uu____22776 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____22776
                                                            pat_exp2
                                                           in
                                                        [uu____22775])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22777,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22778) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22802 =
                                                     let uu____22804 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22804
                                                      in
                                                   if uu____22802
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22814 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22817 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22814
                                                        uu____22817)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22820,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____22821) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____22839 =
                                                     let uu____22841 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____22841
                                                      in
                                                   if uu____22839
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____22851 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____22854 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____22851
                                                        uu____22854)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22857,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head,args)) ->
                                                   let f =
                                                     head_constructor head
                                                      in
                                                   let uu____22904 =
                                                     (let uu____22908 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____22908)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____22904
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____22936 =
                                                          let uu____22941 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____22941
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23027
                                                                     ->
                                                                    match uu____23027
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23049),
                                                                    (ei,uu____23051))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23079
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23079
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23100
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23112
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23112
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23114
                                                                    =
                                                                    let uu____23115
                                                                    =
                                                                    let uu____23120
                                                                    =
                                                                    let uu____23121
                                                                    =
                                                                    let uu____23130
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23130
                                                                     in
                                                                    [uu____23121]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23120
                                                                     in
                                                                    uu____23115
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23114
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____22936
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23153 =
                                                        let uu____23156 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23156 f
                                                         in
                                                      FStar_List.append
                                                        uu____23153
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23159,uu____23160) ->
                                                   []
                                               | uu____23167 ->
                                                   let uu____23172 =
                                                     let uu____23174 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23176 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23174
                                                       uu____23176
                                                      in
                                                   failwith uu____23172
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23205 =
                                                 let uu____23207 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23207
                                                  in
                                               if uu____23205
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23213 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23213
                                                     in
                                                  let uu____23222 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23222 with
                                                  | (k,uu____23228) ->
                                                      let uu____23229 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                         in
                                                      (match uu____23229 with
                                                       | (t1,uu____23237,uu____23238)
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
                                        let uu____23252 =
                                          let eqs =
                                            let uu____23272 =
                                              let uu____23274 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____23274
                                               in
                                            if uu____23272
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____23284 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____23297 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____23298 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____23299 ->
                                                   let uu____23300 =
                                                     let uu____23301 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____23301 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____23300)
                                             in
                                          let uu____23302 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____23302 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____23331 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____23331
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____23333 =
                                                let env1 =
                                                  let uu____23339 =
                                                    FStar_All.pipe_right
                                                      pat_bvs
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____23339
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
                                                   | uu____23360 when
                                                       let uu____23371 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____23371
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
                                                       let uu____23392 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____23393 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____23392,
                                                         uu____23393)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____23408 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____23408
                                                          in
                                                       let uu____23409 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____23410 =
                                                         let uu____23411 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____23411 g_when
                                                          in
                                                       (uu____23409,
                                                         uu____23410)
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
                                                       let uu____23425 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____23425, g_when))
                                                 in
                                              (match uu____23333 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return =
                                                     let c_weak1 =
                                                       let uu____23468 =
                                                         should_return &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____23468
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____23475 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____23475
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
                                                                   let uu____23495
                                                                    =
                                                                    let uu____23500
                                                                    =
                                                                    let uu____23501
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____23501]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____23500
                                                                     in
                                                                   uu____23495
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                            in
                                                         let pat_bv_tms2 =
                                                           let env1 =
                                                             let uu___3026_23538
                                                               =
                                                               FStar_TypeChecker_Env.push_bv
                                                                 env
                                                                 scrutinee
                                                                in
                                                             {
                                                               FStar_TypeChecker_Env.solver
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.solver);
                                                               FStar_TypeChecker_Env.range
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.range);
                                                               FStar_TypeChecker_Env.curmodule
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.curmodule);
                                                               FStar_TypeChecker_Env.gamma
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.gamma);
                                                               FStar_TypeChecker_Env.gamma_sig
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.gamma_sig);
                                                               FStar_TypeChecker_Env.gamma_cache
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.gamma_cache);
                                                               FStar_TypeChecker_Env.modules
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.modules);
                                                               FStar_TypeChecker_Env.expected_typ
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.expected_typ);
                                                               FStar_TypeChecker_Env.sigtab
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.sigtab);
                                                               FStar_TypeChecker_Env.attrtab
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.attrtab);
                                                               FStar_TypeChecker_Env.instantiate_imp
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.instantiate_imp);
                                                               FStar_TypeChecker_Env.effects
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.effects);
                                                               FStar_TypeChecker_Env.generalize
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.generalize);
                                                               FStar_TypeChecker_Env.letrecs
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.letrecs);
                                                               FStar_TypeChecker_Env.top_level
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.top_level);
                                                               FStar_TypeChecker_Env.check_uvars
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.check_uvars);
                                                               FStar_TypeChecker_Env.use_eq
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.use_eq);
                                                               FStar_TypeChecker_Env.use_eq_strict
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.use_eq_strict);
                                                               FStar_TypeChecker_Env.is_iface
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.is_iface);
                                                               FStar_TypeChecker_Env.admit
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.admit);
                                                               FStar_TypeChecker_Env.lax
                                                                 = true;
                                                               FStar_TypeChecker_Env.lax_universes
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.lax_universes);
                                                               FStar_TypeChecker_Env.phase1
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.phase1);
                                                               FStar_TypeChecker_Env.failhard
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.failhard);
                                                               FStar_TypeChecker_Env.nosynth
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.nosynth);
                                                               FStar_TypeChecker_Env.uvar_subtyping
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.uvar_subtyping);
                                                               FStar_TypeChecker_Env.tc_term
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.tc_term);
                                                               FStar_TypeChecker_Env.type_of
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.type_of);
                                                               FStar_TypeChecker_Env.universe_of
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.universe_of);
                                                               FStar_TypeChecker_Env.check_type_of
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.check_type_of);
                                                               FStar_TypeChecker_Env.use_bv_sorts
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.use_bv_sorts);
                                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                               FStar_TypeChecker_Env.normalized_eff_names
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.normalized_eff_names);
                                                               FStar_TypeChecker_Env.fv_delta_depths
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.fv_delta_depths);
                                                               FStar_TypeChecker_Env.proof_ns
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.proof_ns);
                                                               FStar_TypeChecker_Env.synth_hook
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.synth_hook);
                                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                               FStar_TypeChecker_Env.splice
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.splice);
                                                               FStar_TypeChecker_Env.mpreprocess
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.mpreprocess);
                                                               FStar_TypeChecker_Env.postprocess
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.postprocess);
                                                               FStar_TypeChecker_Env.identifier_info
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.identifier_info);
                                                               FStar_TypeChecker_Env.tc_hooks
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.tc_hooks);
                                                               FStar_TypeChecker_Env.dsenv
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.dsenv);
                                                               FStar_TypeChecker_Env.nbe
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.nbe);
                                                               FStar_TypeChecker_Env.strict_args_tab
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.strict_args_tab);
                                                               FStar_TypeChecker_Env.erasable_types_tab
                                                                 =
                                                                 (uu___3026_23538.FStar_TypeChecker_Env.erasable_types_tab)
                                                             }  in
                                                           let uu____23540 =
                                                             let uu____23543
                                                               =
                                                               FStar_List.fold_left2
                                                                 (fun
                                                                    uu____23571
                                                                     ->
                                                                    fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    fun bv 
                                                                    ->
                                                                    match uu____23571
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
                                                                    let uu____23612
                                                                    =
                                                                    let uu____23619
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pat_bv_tm
                                                                    (FStar_Syntax_Subst.subst
                                                                    substs)
                                                                     in
                                                                    let uu____23620
                                                                    =
                                                                    let uu____23631
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t
                                                                     in
                                                                    tc_trivial_guard
                                                                    uu____23631
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23619
                                                                    uu____23620
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23612
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
                                                               uu____23543
                                                               FStar_Pervasives_Native.snd
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____23540
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env1))
                                                            in
                                                         (let uu____23693 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____23693
                                                          then
                                                            let uu____23698 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____23707
                                                                    =
                                                                    let uu____23709
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23709
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23707)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            let uu____23713 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____23722
                                                                    =
                                                                    let uu____23724
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23724
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23722)
                                                                "" pat_bvs
                                                               in
                                                            FStar_Util.print2
                                                              "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                                                              uu____23698
                                                              uu____23713
                                                          else ());
                                                         (let uu____23731 =
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
                                                          let uu____23738 =
                                                            let uu____23743 =
                                                              FStar_TypeChecker_Env.push_bv
                                                                env scrutinee
                                                               in
                                                            FStar_TypeChecker_Util.close_layered_lcomp
                                                              uu____23743
                                                              pat_bvs
                                                              pat_bv_tms2
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23731
                                                            uu____23738)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs c_weak1
                                                      in
                                                   let uu____23746 =
                                                     FStar_TypeChecker_Env.close_guard
                                                       env binders
                                                       g_when_weak
                                                      in
                                                   let uu____23747 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_pat g_branch1
                                                      in
                                                   ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                     (c_weak.FStar_TypeChecker_Common.cflags),
                                                     maybe_return_c_weak,
                                                     uu____23746,
                                                     uu____23747))
                                           in
                                        match uu____23252 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____23802 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____23802
                                              then
                                                let uu____23805 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____23805
                                              else ());
                                             (let uu____23811 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____23828 =
                                                let uu____23829 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____23829 guard
                                                 in
                                              (uu____23811, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____23828,
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
          let uu____23878 = check_let_bound_def true env1 lb  in
          (match uu____23878 with
           | (e1,univ_vars,c1,g1,annotated) ->
               let uu____23904 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23926 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____23926, univ_vars, c1)
                 else
                   (let g11 =
                      let uu____23932 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____23932
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____23933 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____23933 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____23951 =
                          let uu____23964 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____23964  in
                        (match uu____23951 with
                         | (uu____24014,univs,e11,c11,gvs) ->
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
                             let uu____24028 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs, uu____24028)))
                  in
               (match uu____23904 with
                | (g11,e11,univ_vars1,c11) ->
                    let uu____24045 =
                      let uu____24054 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24054
                      then
                        let uu____24065 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24065 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24099 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24099
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24100 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24100, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24112 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24112 with
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
                                  let uu____24136 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24136
                                  then e2
                                  else
                                    ((let uu____24144 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24144
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
                    (match uu____24045 with
                     | (e21,c12) ->
                         ((let uu____24168 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24168
                           then
                             let uu____24171 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24171
                           else ());
                          (let e12 =
                             let uu____24177 = FStar_Options.tcnorm ()  in
                             if uu____24177
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
                           (let uu____24183 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24183
                            then
                              let uu____24186 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24186
                            else ());
                           (let cres =
                              let uu____24192 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24192
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
                                   | (wp,uu____24200)::[] -> wp
                                   | uu____24225 ->
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
                                   let uu____24242 =
                                     let uu____24247 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl ret
                                        in
                                     let uu____24248 =
                                       let uu____24249 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____24258 =
                                         let uu____24269 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____24269]  in
                                       uu____24249 :: uu____24258  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24247 uu____24248
                                      in
                                   uu____24242 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____24306 =
                                     let uu____24311 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl bind
                                        in
                                     let uu____24312 =
                                       let uu____24313 =
                                         let uu____24322 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____24322
                                          in
                                       let uu____24331 =
                                         let uu____24342 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____24359 =
                                           let uu____24370 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____24379 =
                                             let uu____24390 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____24399 =
                                               let uu____24410 =
                                                 let uu____24419 =
                                                   let uu____24420 =
                                                     let uu____24421 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____24421]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____24420 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____24419
                                                  in
                                               [uu____24410]  in
                                             uu____24390 :: uu____24399  in
                                           uu____24370 :: uu____24379  in
                                         uu____24342 :: uu____24359  in
                                       uu____24313 :: uu____24331  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24311 uu____24312
                                      in
                                   uu____24306 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____24498 =
                                   let uu____24499 =
                                     let uu____24510 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____24510]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____24499;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____24498)
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
                            let uu____24538 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____24552 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____24538, uu____24552,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____24553 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____24564 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____24564
        then
          let universe_of_binders bs =
            let uu____24591 =
              FStar_List.fold_left
                (fun uu____24616  ->
                   fun b  ->
                     match uu____24616 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____24591 with | (uu____24664,us) -> FStar_List.rev us
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
            let uu___3158_24700 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3158_24700.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3158_24700.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3158_24700.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3158_24700.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3158_24700.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3158_24700.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3158_24700.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3158_24700.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3158_24700.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3158_24700.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3158_24700.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3158_24700.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3158_24700.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3158_24700.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3158_24700.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3158_24700.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___3158_24700.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___3158_24700.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3158_24700.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3158_24700.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3158_24700.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3158_24700.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3158_24700.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3158_24700.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3158_24700.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3158_24700.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3158_24700.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3158_24700.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3158_24700.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3158_24700.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3158_24700.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3158_24700.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3158_24700.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3158_24700.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3158_24700.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3158_24700.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3158_24700.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3158_24700.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3158_24700.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3158_24700.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3158_24700.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3158_24700.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3158_24700.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3158_24700.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3158_24700.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____24702 =
            let uu____24714 =
              let uu____24715 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____24715 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____24714 lb  in
          (match uu____24702 with
           | (e1,uu____24738,c1,g1,annotated) ->
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
                  (let uu____24752 =
                     let uu____24758 =
                       let uu____24760 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____24762 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24760 uu____24762
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24758)
                      in
                   FStar_Errors.raise_error uu____24752
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24773 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____24773
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3173_24785 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3173_24785.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3173_24785.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____24786 =
                   let uu____24791 =
                     let uu____24792 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____24792]  in
                   FStar_Syntax_Subst.open_term uu____24791 e2  in
                 match uu____24786 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____24836 =
                       let uu____24843 = tc_term env_x e21  in
                       FStar_All.pipe_right uu____24843
                         (fun uu____24869  ->
                            match uu____24869 with
                            | (e22,c2,g2) ->
                                let uu____24885 =
                                  let uu____24890 =
                                    FStar_All.pipe_right
                                      (fun uu____24908  ->
                                         "folding guard g2 of e2 in the lcomp")
                                      (fun uu____24914  ->
                                         FStar_Pervasives_Native.Some
                                           uu____24914)
                                     in
                                  FStar_TypeChecker_Util.strengthen_precondition
                                    uu____24890 env_x e22 c2 g2
                                   in
                                (match uu____24885 with
                                 | (c21,g21) -> (e22, c21, g21)))
                        in
                     (match uu____24836 with
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
                            let uu____24942 =
                              let uu____24949 =
                                let uu____24950 =
                                  let uu____24964 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____24964)  in
                                FStar_Syntax_Syntax.Tm_let uu____24950  in
                              FStar_Syntax_Syntax.mk uu____24949  in
                            uu____24942 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let g21 =
                            let uu____24982 =
                              let uu____24984 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____24984
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____24982 xb g2
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g21
                             in
                          let uu____24987 =
                            let uu____24989 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____24989  in
                          if uu____24987
                          then
                            let tt =
                              let uu____25000 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____25000
                                FStar_Option.get
                               in
                            ((let uu____25006 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25006
                              then
                                let uu____25011 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25013 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25011 uu____25013
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25020 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25020 with
                             | (t,g_ex) ->
                                 ((let uu____25034 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25034
                                   then
                                     let uu____25039 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25041 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25039 uu____25041
                                   else ());
                                  (let uu____25046 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3212_25048 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3212_25048.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3212_25048.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3212_25048.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25046))))))))
      | uu____25049 ->
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
          let uu____25085 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25085 with
           | (lbs1,e21) ->
               let uu____25104 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25104 with
                | (env0,topt) ->
                    let uu____25123 = build_let_rec_env true env0 lbs1  in
                    (match uu____25123 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25146 = check_let_recs rec_env lbs2  in
                         (match uu____25146 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25166 =
                                  let uu____25167 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25167
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25166
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25173 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25173
                                  (fun uu____25190  ->
                                     FStar_Pervasives_Native.Some uu____25190)
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
                                     let uu____25227 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____25261 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____25261)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25227
                                      in
                                   FStar_List.map2
                                     (fun uu____25296  ->
                                        fun lb  ->
                                          match uu____25296 with
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
                                let uu____25344 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____25344
                                 in
                              let uu____25345 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____25345 with
                               | (lbs5,e22) ->
                                   ((let uu____25365 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____25365
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____25366 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____25366, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____25380 -> failwith "Impossible"

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
          let uu____25416 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25416 with
           | (lbs1,e21) ->
               let uu____25435 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25435 with
                | (env0,topt) ->
                    let uu____25454 = build_let_rec_env false env0 lbs1  in
                    (match uu____25454 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25477 =
                           let uu____25484 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____25484
                             (fun uu____25507  ->
                                match uu____25507 with
                                | (lbs3,g) ->
                                    let uu____25526 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____25526))
                            in
                         (match uu____25477 with
                          | (lbs3,g_lbs) ->
                              let uu____25541 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3287_25564 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3287_25564.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3287_25564.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3290_25566 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3290_25566.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____25541 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____25593 = tc_term env2 e21  in
                                   (match uu____25593 with
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
                                          let uu____25617 =
                                            let uu____25618 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____25618 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____25617
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
                                          let uu___3311_25628 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3311_25628.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3311_25628.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3311_25628.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____25636 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____25636))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____25638 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____25638 with
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
                                                  uu____25679 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____25680 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____25680 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3327_25694
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3327_25694.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3327_25694.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3327_25694.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____25695 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____25695))))))))))
      | uu____25696 -> failwith "Impossible"

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
          let uu____25744 = FStar_Options.ml_ish ()  in
          if uu____25744
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____25752 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____25752 with
             | (formals,c) ->
                 let uu____25760 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____25760 with
                  | (actuals,uu____25771,uu____25772) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____25793 =
                          let uu____25799 =
                            let uu____25801 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____25803 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____25801 uu____25803
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____25799)
                           in
                        FStar_Errors.raise_error uu____25793
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____25811 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____25811 actuals
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
                                (let uu____25842 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____25842)
                               in
                            let formals_msg =
                              let n = FStar_List.length formals  in
                              if n = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____25861 = FStar_Util.string_of_int n
                                    in
                                 FStar_Util.format1 "%s arguments"
                                   uu____25861)
                               in
                            let msg =
                              let uu____25866 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____25868 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____25866 uu____25868 formals_msg
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
        let uu____25880 =
          FStar_List.fold_left
            (fun uu____25913  ->
               fun lb  ->
                 match uu____25913 with
                 | (lbs1,env1,g_acc) ->
                     let uu____25938 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____25938 with
                      | (univ_vars,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____25961 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars
                                  in
                               let uu____25980 =
                                 let uu____25987 =
                                   let uu____25988 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____25988
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3373_25999 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3373_25999.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3373_25999.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3373_25999.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3373_25999.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3373_25999.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3373_25999.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3373_25999.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3373_25999.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3373_25999.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3373_25999.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3373_25999.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3373_25999.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3373_25999.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3373_25999.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3373_25999.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3373_25999.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___3373_25999.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3373_25999.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3373_25999.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3373_25999.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3373_25999.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3373_25999.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3373_25999.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3373_25999.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3373_25999.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3373_25999.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3373_25999.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3373_25999.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3373_25999.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3373_25999.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3373_25999.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3373_25999.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3373_25999.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3373_25999.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3373_25999.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3373_25999.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3373_25999.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3373_25999.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3373_25999.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3373_25999.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3373_25999.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3373_25999.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3373_25999.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3373_25999.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3373_25999.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____25987
                                  in
                               match uu____25980 with
                               | (t1,uu____26008,g) ->
                                   let uu____26010 =
                                     let uu____26011 =
                                       let uu____26012 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26012
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26011
                                      in
                                   let uu____26013 = norm env01 t1  in
                                   (uu____26010, uu____26013))
                             in
                          (match uu____25961 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____26033 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____26033
                                 then
                                   let uu___3383_26036 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3383_26036.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3383_26036.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3383_26036.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3383_26036.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3383_26036.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3383_26036.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3383_26036.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3383_26036.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3383_26036.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3383_26036.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3383_26036.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3383_26036.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3383_26036.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3383_26036.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3383_26036.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3383_26036.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___3383_26036.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3383_26036.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3383_26036.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3383_26036.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3383_26036.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3383_26036.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3383_26036.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3383_26036.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3383_26036.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3383_26036.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3383_26036.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3383_26036.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3383_26036.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3383_26036.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3383_26036.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3383_26036.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3383_26036.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3383_26036.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3383_26036.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___3383_26036.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3383_26036.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___3383_26036.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3383_26036.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3383_26036.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3383_26036.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3383_26036.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3383_26036.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3383_26036.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3383_26036.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars, t1)
                                  in
                               let lb1 =
                                 let uu___3386_26050 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3386_26050.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3386_26050.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3386_26050.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3386_26050.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____25880 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26076 =
        let uu____26085 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26111 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26111 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26141 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26141
                       | uu____26148 ->
                           let lb1 =
                             let uu___3403_26151 = lb  in
                             let uu____26152 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26152;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3403_26151.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____26155 =
                             let uu____26162 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____26162
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____26155 with
                            | (e,c,g) ->
                                ((let uu____26171 =
                                    let uu____26173 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____26173  in
                                  if uu____26171
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
        FStar_All.pipe_right uu____26085 FStar_List.unzip  in
      match uu____26076 with
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
        let uu____26229 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____26229 with
        | (env1,uu____26248) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____26256 = check_lbtyp top_level env lb  in
            (match uu____26256 with
             | (topt,wf_annot,univ_vars,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____26305 =
                     tc_maybe_toplevel_term
                       (let uu___3434_26314 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3434_26314.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3434_26314.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3434_26314.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3434_26314.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3434_26314.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3434_26314.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3434_26314.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3434_26314.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3434_26314.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3434_26314.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3434_26314.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3434_26314.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3434_26314.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3434_26314.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3434_26314.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3434_26314.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___3434_26314.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3434_26314.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3434_26314.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3434_26314.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3434_26314.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3434_26314.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3434_26314.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3434_26314.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3434_26314.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3434_26314.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3434_26314.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3434_26314.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3434_26314.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3434_26314.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3434_26314.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3434_26314.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3434_26314.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3434_26314.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3434_26314.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3434_26314.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3434_26314.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3434_26314.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3434_26314.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3434_26314.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3434_26314.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3434_26314.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3434_26314.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3434_26314.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3434_26314.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____26305 with
                   | (e12,c1,g1) ->
                       let uu____26329 =
                         let uu____26334 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____26340  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____26334 e12 c1 wf_annot
                          in
                       (match uu____26329 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____26357 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____26357
                              then
                                let uu____26360 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____26362 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____26364 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____26360 uu____26362 uu____26364
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
            let uu____26403 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26403 with
             | (univ_opening,univ_vars) ->
                 let uu____26436 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars,
                   univ_opening, uu____26436))
        | uu____26441 ->
            let uu____26442 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26442 with
             | (univ_opening,univ_vars) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____26492 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars,
                     univ_opening, uu____26492)
                 else
                   (let uu____26499 = FStar_Syntax_Util.type_u ()  in
                    match uu____26499 with
                    | (k,uu____26519) ->
                        let uu____26520 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____26520 with
                         | (t2,uu____26542,g) ->
                             ((let uu____26545 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____26545
                               then
                                 let uu____26548 =
                                   let uu____26550 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____26550
                                    in
                                 let uu____26551 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____26548 uu____26551
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____26557 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars, univ_opening, uu____26557))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____26563  ->
      match uu____26563 with
      | (x,imp) ->
          let uu____26590 = FStar_Syntax_Util.type_u ()  in
          (match uu____26590 with
           | (tu,u) ->
               ((let uu____26612 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____26612
                 then
                   let uu____26615 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____26617 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____26619 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____26615 uu____26617 uu____26619
                 else ());
                (let uu____26624 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____26624 with
                 | (t,uu____26646,g) ->
                     let uu____26648 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____26664 =
                             tc_tactic FStar_Syntax_Syntax.t_unit
                               FStar_Syntax_Syntax.t_unit env tau
                              in
                           (match uu____26664 with
                            | (tau1,uu____26678,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____26682 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____26648 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3496_26717 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3496_26717.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3496_26717.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____26719 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____26719
                            then
                              let uu____26722 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____26726 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26722
                                uu____26726
                            else ());
                           (let uu____26731 = push_binding env x1  in
                            (x1, uu____26731, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____26743 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____26743
       then
         let uu____26746 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____26746
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26859 = tc_binder env1 b  in
             (match uu____26859 with
              | (b1,env',g,u) ->
                  let uu____26908 = aux env' bs2  in
                  (match uu____26908 with
                   | (bs3,env'1,g',us) ->
                       let uu____26969 =
                         let uu____26970 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____26970  in
                       ((b1 :: bs3), env'1, uu____26969, (u :: us))))
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
          (fun uu____27078  ->
             fun uu____27079  ->
               match (uu____27078, uu____27079) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____27171 = tc_term en1 t  in
                     match uu____27171 with
                     | (t1,uu____27191,g') ->
                         let uu____27193 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____27193)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____27247  ->
             match uu____27247 with
             | (pats1,g) ->
                 let uu____27274 = tc_args en p  in
                 (match uu____27274 with
                  | (args,g') ->
                      let uu____27287 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____27287))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____27300 = tc_maybe_toplevel_term env e  in
      match uu____27300 with
      | (e1,c,g) ->
          let uu____27316 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
             in
          if uu____27316
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let uu____27328 = FStar_TypeChecker_Common.lcomp_comp c  in
             match uu____27328 with
             | (c1,g_c) ->
                 let c2 = norm_c env c1  in
                 let uu____27342 =
                   let uu____27348 =
                     FStar_TypeChecker_Util.is_pure_effect env
                       (FStar_Syntax_Util.comp_effect_name c2)
                      in
                   if uu____27348
                   then
                     let uu____27356 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c2)
                        in
                     (uu____27356, false)
                   else
                     (let uu____27361 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Util.comp_result c2)
                         in
                      (uu____27361, true))
                    in
                 (match uu____27342 with
                  | (target_comp,allow_ghost) ->
                      let uu____27374 =
                        FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                      (match uu____27374 with
                       | FStar_Pervasives_Native.Some g' ->
                           let uu____27384 =
                             FStar_TypeChecker_Common.lcomp_of_comp
                               target_comp
                              in
                           let uu____27385 =
                             let uu____27386 =
                               FStar_TypeChecker_Env.conj_guard g_c g'  in
                             FStar_TypeChecker_Env.conj_guard g1 uu____27386
                              in
                           (e1, uu____27384, uu____27385)
                       | uu____27387 ->
                           if allow_ghost
                           then
                             let uu____27397 =
                               FStar_TypeChecker_Err.expected_ghost_expression
                                 e1 c2
                                in
                             FStar_Errors.raise_error uu____27397
                               e1.FStar_Syntax_Syntax.pos
                           else
                             (let uu____27411 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e1 c2
                                 in
                              FStar_Errors.raise_error uu____27411
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
      let uu____27435 = tc_tot_or_gtot_term env t  in
      match uu____27435 with
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
        let uu____27466 = tc_check_tot_or_gtot_term env t k  in
        match uu____27466 with
        | (t1,uu____27474,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____27495 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____27495
       then
         let uu____27500 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____27500
       else ());
      (let env1 =
         let uu___3588_27506 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3588_27506.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3588_27506.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3588_27506.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3588_27506.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3588_27506.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3588_27506.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3588_27506.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3588_27506.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3588_27506.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3588_27506.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3588_27506.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3588_27506.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3588_27506.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3588_27506.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3588_27506.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___3588_27506.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___3588_27506.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3588_27506.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3588_27506.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3588_27506.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3588_27506.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3588_27506.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3588_27506.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3588_27506.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3588_27506.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3588_27506.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3588_27506.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3588_27506.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3588_27506.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3588_27506.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3588_27506.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3588_27506.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3588_27506.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3588_27506.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3588_27506.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3588_27506.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3588_27506.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3588_27506.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3588_27506.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3588_27506.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3588_27506.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3588_27506.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3588_27506.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3588_27506.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____27514 =
         try
           (fun uu___3592_27528  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____27549) ->
             let uu____27552 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____27552
          in
       match uu____27514 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____27570 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____27570
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____27581 =
                let uu____27587 =
                  let uu____27589 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____27589
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____27587)
                 in
              let uu____27593 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____27581 uu____27593))
  
let level_of_type_fail :
  'uuuuuu27609 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'uuuuuu27609
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____27627 =
          let uu____27633 =
            let uu____27635 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____27635 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____27633)  in
        let uu____27639 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____27627 uu____27639
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____27673 =
            let uu____27674 = FStar_Syntax_Util.unrefine t1  in
            uu____27674.FStar_Syntax_Syntax.n  in
          match uu____27673 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____27678 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____27684 = FStar_Syntax_Util.type_u ()  in
                 match uu____27684 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3624_27692 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3624_27692.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3624_27692.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3624_27692.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3624_27692.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3624_27692.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3624_27692.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3624_27692.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3624_27692.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3624_27692.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3624_27692.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3624_27692.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3624_27692.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3624_27692.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3624_27692.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3624_27692.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3624_27692.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3624_27692.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3624_27692.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3624_27692.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3624_27692.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3624_27692.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3624_27692.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3624_27692.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3624_27692.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3624_27692.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3624_27692.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3624_27692.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3624_27692.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3624_27692.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3624_27692.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3624_27692.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3624_27692.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3624_27692.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3624_27692.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3624_27692.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3624_27692.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3624_27692.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3624_27692.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3624_27692.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3624_27692.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3624_27692.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3624_27692.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3624_27692.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3624_27692.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3624_27692.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____27697 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____27697
                       | uu____27699 ->
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
      let uu____27716 =
        let uu____27717 = FStar_Syntax_Subst.compress e  in
        uu____27717.FStar_Syntax_Syntax.n  in
      match uu____27716 with
      | FStar_Syntax_Syntax.Tm_bvar uu____27720 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____27723 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____27739 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____27756) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____27801) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n -> n.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27808 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27808 with | ((uu____27817,t),uu____27819) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27825 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____27825
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27828,(FStar_Util.Inl t,uu____27830),uu____27831) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27878,(FStar_Util.Inr c,uu____27880),uu____27881) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27929 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27938;
             FStar_Syntax_Syntax.vars = uu____27939;_},us)
          ->
          let uu____27945 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27945 with
           | ((us',t),uu____27956) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27963 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27963)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____27982 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27984 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27993) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28020 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28020 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28040  ->
                      match uu____28040 with
                      | (b,uu____28048) ->
                          let uu____28053 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28053) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28058 = universe_of_aux env res  in
                 level_of_type env res uu____28058  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____28169 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____28185 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____28215 ->
                let uu____28216 = universe_of_aux env hd2  in
                (uu____28216, args1)
            | FStar_Syntax_Syntax.Tm_name uu____28227 ->
                let uu____28228 = universe_of_aux env hd2  in
                (uu____28228, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____28239 ->
                let uu____28252 = universe_of_aux env hd2  in
                (uu____28252, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____28263 ->
                let uu____28270 = universe_of_aux env hd2  in
                (uu____28270, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____28281 ->
                let uu____28308 = universe_of_aux env hd2  in
                (uu____28308, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____28319 ->
                let uu____28326 = universe_of_aux env hd2  in
                (uu____28326, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____28337 ->
                let uu____28338 = universe_of_aux env hd2  in
                (uu____28338, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____28349 ->
                let uu____28364 = universe_of_aux env hd2  in
                (uu____28364, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____28375 ->
                let uu____28382 = universe_of_aux env hd2  in
                (uu____28382, args1)
            | FStar_Syntax_Syntax.Tm_type uu____28393 ->
                let uu____28394 = universe_of_aux env hd2  in
                (uu____28394, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____28405,hd3::uu____28407) ->
                let uu____28472 = FStar_Syntax_Subst.open_branch hd3  in
                (match uu____28472 with
                 | (uu____28487,uu____28488,hd4) ->
                     let uu____28506 = FStar_Syntax_Util.head_and_args hd4
                        in
                     (match uu____28506 with
                      | (hd5,args') ->
                          type_of_head retry hd5
                            (FStar_List.append args' args1)))
            | uu____28571 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____28573 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____28573 with
                 | (hd3,args2) -> type_of_head false hd3 args2)
            | uu____28631 ->
                let uu____28632 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____28632 with
                 | (env1,uu____28654) ->
                     let env2 =
                       let uu___3785_28660 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3785_28660.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3785_28660.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3785_28660.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3785_28660.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3785_28660.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3785_28660.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3785_28660.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3785_28660.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3785_28660.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3785_28660.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3785_28660.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3785_28660.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3785_28660.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3785_28660.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3785_28660.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3785_28660.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___3785_28660.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3785_28660.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3785_28660.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3785_28660.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3785_28660.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3785_28660.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3785_28660.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3785_28660.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3785_28660.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3785_28660.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3785_28660.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3785_28660.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3785_28660.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3785_28660.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3785_28660.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3785_28660.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3785_28660.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3785_28660.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3785_28660.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3785_28660.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3785_28660.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3785_28660.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3785_28660.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3785_28660.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3785_28660.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3785_28660.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3785_28660.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____28665 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____28665
                       then
                         let uu____28670 =
                           let uu____28672 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____28672  in
                         let uu____28673 =
                           FStar_Syntax_Print.term_to_string hd2  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____28670 uu____28673
                       else ());
                      (let uu____28678 = tc_term env2 hd2  in
                       match uu____28678 with
                       | (uu____28699,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____28700;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____28702;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____28703;_},g)
                           ->
                           ((let uu____28721 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____28721
                               (fun uu____28722  -> ()));
                            (t, args1)))))
             in
          let uu____28733 = type_of_head true hd args  in
          (match uu____28733 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____28772 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____28772 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst res1
                    else
                      (let uu____28800 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____28800)))
      | FStar_Syntax_Syntax.Tm_match (uu____28802,hd::uu____28804) ->
          let uu____28869 = FStar_Syntax_Subst.open_branch hd  in
          (match uu____28869 with
           | (uu____28870,uu____28871,hd1) -> universe_of_aux env hd1)
      | FStar_Syntax_Syntax.Tm_match (uu____28889,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____28936 = universe_of_aux env e  in
      level_of_type env e uu____28936
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0  ->
    fun tps  ->
      let uu____28960 = tc_binders env0 tps  in
      match uu____28960 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____29018 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29036 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29042 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29042
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29044 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29044
            (fun uu____29058  ->
               match uu____29058 with
               | (t2,uu____29066) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29068;
             FStar_Syntax_Syntax.vars = uu____29069;_},us)
          ->
          let uu____29075 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29075
            (fun uu____29089  ->
               match uu____29089 with
               | (t2,uu____29097) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29098) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29100 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29100
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29102 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29102
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29107;_})
          ->
          let mk_comp =
            let uu____29151 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____29151
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____29182 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____29182
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____29252 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____29252
                 (fun u  ->
                    let uu____29260 =
                      let uu____29263 =
                        let uu____29270 =
                          let uu____29271 =
                            let uu____29286 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____29286)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____29271  in
                        FStar_Syntax_Syntax.mk uu____29270  in
                      uu____29263 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____29260))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____29323 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____29323 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____29382 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____29382
                       (fun uc  ->
                          let uu____29390 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____29390)
                 | (x,imp)::bs3 ->
                     let uu____29416 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____29416
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____29425 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____29445) ->
          let uu____29450 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____29450
            (fun u_x  ->
               let uu____29458 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____29458)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____29463;
             FStar_Syntax_Syntax.vars = uu____29464;_},a::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____29543 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29543 with
           | (unary_op,uu____29563) ->
               let head =
                 let uu____29591 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____29591
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
             FStar_Syntax_Syntax.pos = uu____29639;
             FStar_Syntax_Syntax.vars = uu____29640;_},a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____29736 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29736 with
           | (unary_op,uu____29756) ->
               let head =
                 let uu____29784 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   FStar_Pervasives_Native.None uu____29784
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
             FStar_Syntax_Syntax.pos = uu____29840;
             FStar_Syntax_Syntax.vars = uu____29841;_},uu____29842::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29881;
             FStar_Syntax_Syntax.vars = uu____29882;_},(t2,uu____29884)::uu____29885::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let t_hd = type_of_well_typed_term env hd  in
          let rec aux t_hd1 =
            let uu____29981 =
              let uu____29982 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____29982.FStar_Syntax_Syntax.n  in
            match uu____29981 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30055 = FStar_Util.first_N n_args bs  in
                    match uu____30055 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____30143 =
                          let uu____30148 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____30148  in
                        (match uu____30143 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____30202 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____30202 with
                       | (bs1,c1) ->
                           let uu____30223 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____30223
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____30305  ->
                     match uu____30305 with
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
                         let uu____30381 = FStar_Syntax_Subst.subst subst t2
                            in
                         FStar_Pervasives_Native.Some uu____30381)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____30383) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____30389,uu____30390) ->
                aux t2
            | uu____30431 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30432,(FStar_Util.Inl t2,uu____30434),uu____30435) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30482,(FStar_Util.Inr c,uu____30484),uu____30485) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____30550 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____30550
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____30558) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____30563 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____30586 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____30600 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____30611 = type_of_well_typed_term env t  in
      match uu____30611 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____30617;
            FStar_Syntax_Syntax.vars = uu____30618;_}
          -> FStar_Pervasives_Native.Some u
      | uu____30621 -> FStar_Pervasives_Native.None

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
            let uu___4064_30649 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4064_30649.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4064_30649.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4064_30649.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4064_30649.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4064_30649.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4064_30649.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4064_30649.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4064_30649.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4064_30649.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4064_30649.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4064_30649.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4064_30649.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4064_30649.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4064_30649.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4064_30649.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4064_30649.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4064_30649.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4064_30649.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4064_30649.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4064_30649.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4064_30649.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4064_30649.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4064_30649.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4064_30649.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4064_30649.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4064_30649.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4064_30649.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4064_30649.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4064_30649.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4064_30649.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4064_30649.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4064_30649.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4064_30649.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4064_30649.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4064_30649.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4064_30649.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4064_30649.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4064_30649.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4064_30649.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4064_30649.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4064_30649.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4064_30649.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4064_30649.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4064_30649.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4064_30649.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30656 =
            if must_total
            then
              let uu____30658 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30658 with | (uu____30665,uu____30666,g) -> g
            else
              (let uu____30670 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30670 with | (uu____30677,uu____30678,g) -> g)
             in
          let uu____30680 = type_of_well_typed_term env2 t  in
          match uu____30680 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____30685 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____30685
                then
                  let uu____30690 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____30692 = FStar_Syntax_Print.term_to_string t  in
                  let uu____30694 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____30696 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____30690 uu____30692 uu____30694 uu____30696
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____30705 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____30705
                 then
                   let uu____30710 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____30712 = FStar_Syntax_Print.term_to_string t  in
                   let uu____30714 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____30716 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____30710
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____30712 uu____30714 uu____30716
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
            let uu___4095_30753 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4095_30753.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4095_30753.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4095_30753.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4095_30753.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4095_30753.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4095_30753.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4095_30753.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4095_30753.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4095_30753.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4095_30753.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4095_30753.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4095_30753.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4095_30753.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4095_30753.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4095_30753.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4095_30753.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4095_30753.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___4095_30753.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___4095_30753.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4095_30753.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4095_30753.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4095_30753.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4095_30753.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4095_30753.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4095_30753.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4095_30753.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4095_30753.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4095_30753.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4095_30753.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4095_30753.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4095_30753.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4095_30753.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4095_30753.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4095_30753.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4095_30753.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___4095_30753.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4095_30753.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4095_30753.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4095_30753.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4095_30753.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4095_30753.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4095_30753.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4095_30753.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4095_30753.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4095_30753.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30760 =
            if must_total
            then
              let uu____30762 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30762 with | (uu____30769,uu____30770,g) -> g
            else
              (let uu____30774 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30774 with | (uu____30781,uu____30782,g) -> g)
             in
          let uu____30784 =
            let uu____30786 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____30786  in
          if uu____30784
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  