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
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe)
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
      FStar_TypeChecker_Env.nbe = (uu___11_13.FStar_TypeChecker_Env.nbe)
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
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
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
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____425  ->
           let uu____426 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____426 t)
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
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
                 let uu____485 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                   uu____485
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_Syntax_Syntax.res_typ  in
           let uu____488 =
             let uu____495 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____495 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____505 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t'
                    in
                 (match uu____505 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____519 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____519 with
                       | (e2,g) ->
                           ((let uu____533 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____533
                             then
                               let uu____536 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____538 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____540 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____542 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____536 uu____538 uu____540 uu____542
                             else ());
                            (let msg =
                               let uu____554 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g
                                  in
                               if uu____554
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _583  ->
                                      FStar_Pervasives_Native.Some _583)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard  in
                             let lc2 =
                               let uu____586 =
                                 (FStar_All.pipe_right tlc FStar_Util.is_left)
                                   &&
                                   (FStar_TypeChecker_Util.should_return env
                                      (FStar_Pervasives_Native.Some e2) lc1)
                                  in
                               if uu____586
                               then
                                 let uu____594 =
                                   let uu____595 =
                                     FStar_TypeChecker_Util.lcomp_univ_opt
                                       lc1
                                      in
                                   FStar_TypeChecker_Util.return_value env
                                     uu____595 t1 e2
                                    in
                                 FStar_All.pipe_right uu____594
                                   FStar_Syntax_Util.lcomp_of_comp
                               else lc1  in
                             let uu____600 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc2 g1
                                in
                             match uu____600 with
                             | (lc3,g2) ->
                                 let uu____613 = set_lcomp_result lc3 t'  in
                                 ((memo_tk e2 t'), uu____613, g2)))))
              in
           match uu____488 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____651 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____651 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____661 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____661 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____714 = ec  in
        match uu____714 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____737 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____737
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____742 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____742
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____748 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____770 -> (copt, c, false)
              | FStar_Pervasives_Native.None  ->
                  let uu____775 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____778 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____778))
                     in
                  if uu____775
                  then
                    let uu____790 =
                      let uu____793 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____793  in
                    (uu____790, c, false)
                  else
                    (let uu____800 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____800
                     then
                       let uu____812 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____812, false)
                     else
                       (let uu____819 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____819
                        then
                          let uu____831 =
                            let uu____834 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____834  in
                          (uu____831, c, false)
                        else
                          (let uu____841 =
                             FStar_Options.trivial_pre_for_unannotated_effectful_fns
                               ()
                              in
                           if uu____841
                           then
                             let uu____853 =
                               let uu____856 =
                                 let uu____857 =
                                   FStar_All.pipe_right ct
                                     (env.FStar_TypeChecker_Env.universe_of
                                        env)
                                    in
                                 FStar_TypeChecker_Env.null_wp_for_eff env
                                   (FStar_Syntax_Util.comp_effect_name c)
                                   uu____857 ct
                                  in
                               FStar_Pervasives_Native.Some uu____856  in
                             (uu____853, c, true)
                           else (FStar_Pervasives_Native.None, c, true))))
               in
            (match uu____748 with
             | (expected_c_opt,c1,should_return_c) ->
                 let c0 = c1  in
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____893 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____893
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____896 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low
                           in
                        if uu____896
                        then
                          let uu____900 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____902 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____904 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____900 uu____902 uu____904
                        else ());
                       (let uu____909 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____909 with
                        | (e1,uu____923,g) ->
                            let g1 =
                              let uu____926 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____926
                                "could not prove post-condition" g
                               in
                            ((let uu____929 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____929
                              then
                                let uu____932 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____934 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____932 uu____934
                              else ());
                             (let e2 =
                                FStar_TypeChecker_Util.maybe_lift env e1
                                  (FStar_Syntax_Util.comp_effect_name c4)
                                  (FStar_Syntax_Util.comp_effect_name
                                     expected_c)
                                  (FStar_Syntax_Util.comp_result c4)
                                 in
                              (e2,
                                (if should_return_c then c0 else expected_c),
                                g1)))))))
  
let no_logical_guard :
  'Auu____952 'Auu____953 .
    FStar_TypeChecker_Env.env ->
      ('Auu____952 * 'Auu____953 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____952 * 'Auu____953 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____975  ->
      match uu____975 with
      | (te,kt,f) ->
          let uu____985 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____985 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____993 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____999 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____993 uu____999)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1012 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1012 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1017 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1017
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1059 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1059 with
        | (head1,args) ->
            let uu____1104 =
              let uu____1119 =
                let uu____1120 = FStar_Syntax_Util.un_uinst head1  in
                uu____1120.FStar_Syntax_Syntax.n  in
              (uu____1119, args)  in
            (match uu____1104 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1136) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1163,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1164))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1241,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1242))::(pat,FStar_Pervasives_Native.None
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
             | uu____1326 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1357 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1357) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1393 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1400 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1393 uu____1400  in
          let uu____1401 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1428  ->
                    match uu____1428 with
                    | (b,uu____1435) ->
                        let uu____1436 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1436))
             in
          match uu____1401 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1443) ->
              let uu____1448 =
                let uu____1454 =
                  let uu____1456 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1456
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1454)  in
              FStar_Errors.log_issue rng uu____1448
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1482 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1482 with
        | (head1,args) ->
            let uu____1527 =
              let uu____1542 =
                let uu____1543 = FStar_Syntax_Util.un_uinst head1  in
                uu____1543.FStar_Syntax_Syntax.n  in
              (uu____1542, args)  in
            (match uu____1527 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1559) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1581::(hd1,uu____1583)::(tl1,uu____1585)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1652 = pat_terms hd1  in
                 let uu____1655 = pat_terms tl1  in
                 FStar_List.append uu____1652 uu____1655
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1659::(pat,uu____1661)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1746 -> [])
         in
      let rec aux t1 =
        let uu____1771 =
          let uu____1772 = FStar_Syntax_Subst.compress t1  in
          uu____1772.FStar_Syntax_Syntax.n  in
        match uu____1771 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1777 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1778 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1779 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1780 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1793 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1794 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1795 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1814 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1829 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1836 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1859 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1873 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1896 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1904 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____1904 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____1937 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____1954  ->
                   match uu____1954 with
                   | (t3,uu____1966) ->
                       let uu____1971 = aux t3  in
                       FStar_List.append acc uu____1971) uu____1937 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1975,uu____1976) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2018) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2024) -> aux t2  in
      let tlist =
        let uu____2032 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2032 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = (Prims.parse_int "0")
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2055 =
                    let uu____2057 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2057  in
                  Prims.op_Hat s uu____2055) "" tlist
            in
         let uu____2061 =
           let uu____2067 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2067)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2061)
  
let check_smt_pat :
  'Auu____2082 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2082) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2123 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2123
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2126;
                  FStar_Syntax_Syntax.effect_name = uu____2127;
                  FStar_Syntax_Syntax.result_typ = uu____2128;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2132)::[];
                  FStar_Syntax_Syntax.flags = uu____2133;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2195 -> failwith "Impossible"
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
              let uu___350_2258 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___350_2258.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___350_2258.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___350_2258.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___350_2258.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___350_2258.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___350_2258.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___350_2258.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___350_2258.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___350_2258.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___350_2258.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___350_2258.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___350_2258.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___350_2258.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___350_2258.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___350_2258.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___350_2258.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___350_2258.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___350_2258.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___350_2258.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___350_2258.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___350_2258.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___350_2258.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___350_2258.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___350_2258.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___350_2258.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___350_2258.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___350_2258.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___350_2258.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___350_2258.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___350_2258.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___350_2258.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___350_2258.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___350_2258.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___350_2258.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___350_2258.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___350_2258.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.postprocess =
                  (uu___350_2258.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___350_2258.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___350_2258.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___350_2258.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___350_2258.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___350_2258.FStar_TypeChecker_Env.nbe)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2284 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2284
               then
                 let uu____2287 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2290 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2287 uu____2290
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2324  ->
                         match uu____2324 with
                         | (b,uu____2334) ->
                             let t =
                               let uu____2340 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2340
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2343 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2344 -> []
                              | uu____2359 ->
                                  let uu____2360 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2360])))
                  in
               let as_lex_list dec =
                 let uu____2373 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2373 with
                 | (head1,uu____2393) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2421 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2429 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2438  ->
                         match uu___1_2438 with
                         | FStar_Syntax_Syntax.DECREASES uu____2440 -> true
                         | uu____2444 -> false))
                  in
               match uu____2429 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2451 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2472 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2501 =
              match uu____2501 with
              | (l,t,u_names) ->
                  let uu____2525 =
                    let uu____2526 = FStar_Syntax_Subst.compress t  in
                    uu____2526.FStar_Syntax_Syntax.n  in
                  (match uu____2525 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2585  ->
                                 match uu____2585 with
                                 | (x,imp) ->
                                     let uu____2604 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2604
                                     then
                                       let uu____2613 =
                                         let uu____2614 =
                                           let uu____2617 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2617
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2614
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2613, imp)
                                     else (x, imp)))
                          in
                       let uu____2624 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2624 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2645 =
                                let uu____2650 =
                                  let uu____2651 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2660 =
                                    let uu____2671 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2671]  in
                                  uu____2651 :: uu____2660  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2650
                                 in
                              uu____2645 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2706 = FStar_Util.prefix formals2  in
                            (match uu____2706 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___417_2769 = last1  in
                                   let uu____2770 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___417_2769.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___417_2769.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2770
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2806 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____2806
                                   then
                                     let uu____2809 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2811 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2813 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2809 uu____2811 uu____2813
                                   else ());
                                  (l, t', u_names))))
                   | uu____2820 ->
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
               let uu____2884 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2884)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3497 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3497
       then
         let uu____3500 =
           let uu____3502 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3502  in
         let uu____3504 = FStar_Syntax_Print.term_to_string e  in
         let uu____3506 =
           let uu____3508 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3508  in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3500
           uu____3504 uu____3506
       else ());
      (let uu____3512 =
         FStar_Util.record_time
           (fun uu____3531  ->
              tc_maybe_toplevel_term
                (let uu___436_3534 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___436_3534.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___436_3534.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___436_3534.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___436_3534.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___436_3534.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___436_3534.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___436_3534.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___436_3534.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___436_3534.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___436_3534.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___436_3534.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___436_3534.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___436_3534.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___436_3534.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___436_3534.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___436_3534.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___436_3534.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___436_3534.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___436_3534.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___436_3534.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___436_3534.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___436_3534.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___436_3534.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___436_3534.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___436_3534.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___436_3534.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___436_3534.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___436_3534.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___436_3534.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___436_3534.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___436_3534.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___436_3534.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___436_3534.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___436_3534.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___436_3534.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___436_3534.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___436_3534.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___436_3534.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___436_3534.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___436_3534.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___436_3534.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___436_3534.FStar_TypeChecker_Env.nbe)
                 }) e)
          in
       match uu____3512 with
       | (r,ms) ->
           ((let uu____3559 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3559
             then
               ((let uu____3563 =
                   let uu____3565 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3565
                    in
                 let uu____3567 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3569 =
                   let uu____3571 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3571  in
                 let uu____3572 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3563 uu____3567 uu____3569 uu____3572);
                (let uu____3575 = r  in
                 match uu____3575 with
                 | (e1,uu____3583,uu____3584) ->
                     let uu____3585 =
                       let uu____3587 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3587
                        in
                     let uu____3589 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3591 =
                       let uu____3593 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3593  in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3585
                       uu____3589 uu____3591))
             else ());
            r))

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____3611 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3611
       then
         let uu____3614 =
           let uu____3616 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3616  in
         let uu____3618 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3620 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3614 uu____3618
           uu____3620
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3631 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3661 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3668 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3681 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3682 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3683 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3684 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3685 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3704 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3719 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3726 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3742 =
             match uu___2_3742 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3748 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3764 =
                 let uu____3765 = FStar_Syntax_Subst.compress t  in
                 uu____3765.FStar_Syntax_Syntax.n  in
               match uu____3764 with
               | FStar_Syntax_Syntax.Tm_name uu____3769 -> true
               | uu____3771 -> false  in
             FStar_Util.for_some
               (fun uu____3781  ->
                  match uu____3781 with
                  | (uu____3787,t) ->
                      let uu____3789 = is_name1 t  in
                      Prims.op_Negation uu____3789)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3808  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3851  ->
                       match uu____3851 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___509_3880 = qi  in
                  let uu____3881 =
                    FStar_List.map
                      (fun uu____3909  ->
                         match uu____3909 with
                         | ((bv,uu____3925),bv') ->
                             let uu____3937 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____3937)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___509_3880.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3881
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
                         let uu____3949 =
                           let uu____3956 =
                             let uu____3957 =
                               let uu____3971 =
                                 let uu____3974 =
                                   let uu____3975 =
                                     let uu____3982 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____3982
                                      in
                                   [uu____3975]  in
                                 FStar_Syntax_Subst.close uu____3974 t  in
                               ((false, [lb]), uu____3971)  in
                             FStar_Syntax_Syntax.Tm_let uu____3957  in
                           FStar_Syntax_Syntax.mk uu____3956  in
                         uu____3949 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4018 =
                  FStar_List.fold_right
                    (fun uu____4054  ->
                       fun uu____4055  ->
                         match (uu____4054, uu____4055) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4124 = tc_term env_tm tm  in
                             (match uu____4124 with
                              | (tm1,uu____4142,g) ->
                                  let uu____4144 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4144))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4018 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___537_4186 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___537_4186.FStar_Syntax_Syntax.qkind);
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
                let uu____4205 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4205 with
                 | (env',uu____4219) ->
                     let uu____4224 =
                       tc_term
                         (let uu___546_4233 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___546_4233.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___546_4233.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___546_4233.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___546_4233.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___546_4233.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___546_4233.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___546_4233.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___546_4233.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___546_4233.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___546_4233.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___546_4233.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___546_4233.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___546_4233.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___546_4233.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___546_4233.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___546_4233.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___546_4233.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___546_4233.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___546_4233.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___546_4233.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___546_4233.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___546_4233.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___546_4233.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___546_4233.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___546_4233.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___546_4233.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___546_4233.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___546_4233.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___546_4233.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___546_4233.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___546_4233.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___546_4233.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___546_4233.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___546_4233.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___546_4233.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___546_4233.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___546_4233.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___546_4233.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___546_4233.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___546_4233.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___546_4233.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___546_4233.FStar_TypeChecker_Env.nbe)
                          }) qt
                        in
                     (match uu____4224 with
                      | (qt1,uu____4242,uu____4243) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4249 =
                            let uu____4256 =
                              let uu____4261 =
                                FStar_Syntax_Util.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4261  in
                            value_check_expected_typ env1 top uu____4256
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4249 with
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
           { FStar_Syntax_Syntax.blob = uu____4278;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4279;
             FStar_Syntax_Syntax.ltyp = uu____4280;
             FStar_Syntax_Syntax.rng = uu____4281;_}
           ->
           let uu____4292 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4292
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4299 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4299 with
            | (e2,c,g) ->
                let g1 =
                  let uu___576_4316 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___576_4316.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___576_4316.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___576_4316.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____4317 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4317, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4359 = FStar_Syntax_Util.type_u ()  in
           (match uu____4359 with
            | (t,u) ->
                let uu____4372 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4372 with
                 | (e2,c,g) ->
                     let uu____4388 =
                       let uu____4405 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4405 with
                       | (env2,uu____4429) -> tc_smt_pats env2 pats  in
                     (match uu____4388 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___599_4467 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___599_4467.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___599_4467.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___599_4467.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____4468 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4487 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4468, c, uu____4487))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4493 =
             let uu____4494 = FStar_Syntax_Subst.compress e1  in
             uu____4494.FStar_Syntax_Syntax.n  in
           (match uu____4493 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4503,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4505;
                               FStar_Syntax_Syntax.lbtyp = uu____4506;
                               FStar_Syntax_Syntax.lbeff = uu____4507;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4509;
                               FStar_Syntax_Syntax.lbpos = uu____4510;_}::[]),e2)
                ->
                let uu____4541 =
                  let uu____4548 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4548 e11  in
                (match uu____4541 with
                 | (e12,c1,g1) ->
                     let uu____4558 = tc_term env1 e2  in
                     (match uu____4558 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ
                             in
                          let attrs =
                            let uu____4582 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_Syntax_Syntax.eff_name
                               in
                            if uu____4582
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4592 =
                              let uu____4599 =
                                let uu____4600 =
                                  let uu____4614 =
                                    let uu____4622 =
                                      let uu____4625 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4625]  in
                                    (false, uu____4622)  in
                                  (uu____4614, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4600  in
                              FStar_Syntax_Syntax.mk uu____4599  in
                            uu____4592 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ
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
                          let uu____4649 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4649)))
            | uu____4650 ->
                let uu____4651 = tc_term env1 e1  in
                (match uu____4651 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4673) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4685) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4704 = tc_term env1 e1  in
           (match uu____4704 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4728) ->
           let uu____4775 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4775 with
            | (env0,uu____4789) ->
                let uu____4794 = tc_comp env0 expected_c  in
                (match uu____4794 with
                 | (expected_c1,uu____4808,g) ->
                     let uu____4810 =
                       let uu____4817 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4817 e1  in
                     (match uu____4810 with
                      | (e2,c',g') ->
                          let uu____4827 =
                            let uu____4834 =
                              let uu____4839 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____4839)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____4834
                             in
                          (match uu____4827 with
                           | (e3,expected_c2,g'') ->
                               let uu____4849 = tc_tactic_opt env0 topt  in
                               (match uu____4849 with
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
                                      FStar_Syntax_Util.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____4909 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____4909
                                       in
                                    let uu____4910 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____4910 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____4927 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____4927
                                            in
                                         let uu____4928 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____4928)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____4932) ->
           let uu____4979 = FStar_Syntax_Util.type_u ()  in
           (match uu____4979 with
            | (k,u) ->
                let uu____4992 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____4992 with
                 | (t1,uu____5006,f) ->
                     let uu____5008 = tc_tactic_opt env1 topt  in
                     (match uu____5008 with
                      | (topt1,gtac) ->
                          let uu____5027 =
                            let uu____5034 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5034 e1  in
                          (match uu____5027 with
                           | (e2,c,g) ->
                               let uu____5044 =
                                 let uu____5049 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5055  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5049 e2 c f
                                  in
                               (match uu____5044 with
                                | (c1,f1) ->
                                    let uu____5065 =
                                      let uu____5072 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5072
                                        c1
                                       in
                                    (match uu____5065 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5119 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5119
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5121 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5121)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5122;
              FStar_Syntax_Syntax.vars = uu____5123;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5202 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5202 with
            | (unary_op1,uu____5226) ->
                let head1 =
                  let uu____5254 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5254
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
              FStar_Syntax_Syntax.pos = uu____5302;
              FStar_Syntax_Syntax.vars = uu____5303;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5382 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5382 with
            | (unary_op1,uu____5406) ->
                let head1 =
                  let uu____5434 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5434
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
                (FStar_Const.Const_reflect uu____5482);
              FStar_Syntax_Syntax.pos = uu____5483;
              FStar_Syntax_Syntax.vars = uu____5484;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5563 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5563 with
            | (unary_op1,uu____5587) ->
                let head1 =
                  let uu____5615 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5615
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
              FStar_Syntax_Syntax.pos = uu____5663;
              FStar_Syntax_Syntax.vars = uu____5664;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5760 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5760 with
            | (unary_op1,uu____5784) ->
                let head1 =
                  let uu____5812 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5812
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
              FStar_Syntax_Syntax.pos = uu____5868;
              FStar_Syntax_Syntax.vars = uu____5869;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____5907 =
             let uu____5914 =
               let uu____5915 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5915  in
             tc_term uu____5914 e1  in
           (match uu____5907 with
            | (e2,c,g) ->
                let uu____5939 = FStar_Syntax_Util.head_and_args top  in
                (match uu____5939 with
                 | (head1,uu____5963) ->
                     let uu____5988 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6021 =
                       let uu____6022 =
                         let uu____6023 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6023  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____6022
                        in
                     (uu____5988, uu____6021, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6024;
              FStar_Syntax_Syntax.vars = uu____6025;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6078 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6078 with
            | (head1,uu____6102) ->
                let env' =
                  let uu____6128 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6128  in
                let uu____6129 = tc_term env' r  in
                (match uu____6129 with
                 | (er,uu____6143,gr) ->
                     let uu____6145 = tc_term env1 t  in
                     (match uu____6145 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6162 =
                            let uu____6163 =
                              let uu____6168 =
                                let uu____6169 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6178 =
                                  let uu____6189 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6189]  in
                                uu____6169 :: uu____6178  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6168
                               in
                            uu____6163 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6162, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6222;
              FStar_Syntax_Syntax.vars = uu____6223;_},uu____6224)
           ->
           let uu____6249 =
             let uu____6255 =
               let uu____6257 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6257  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6255)  in
           FStar_Errors.raise_error uu____6249 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6267;
              FStar_Syntax_Syntax.vars = uu____6268;_},uu____6269)
           ->
           let uu____6294 =
             let uu____6300 =
               let uu____6302 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6302  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6300)  in
           FStar_Errors.raise_error uu____6294 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6312;
              FStar_Syntax_Syntax.vars = uu____6313;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6360 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6360 with
             | (env0,uu____6374) ->
                 let uu____6379 = tc_term env0 e1  in
                 (match uu____6379 with
                  | (e2,c,g) ->
                      let uu____6395 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6395 with
                       | (reify_op,uu____6419) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_Syntax_Syntax.res_typ
                              in
                           let ef =
                             let uu____6446 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_Syntax_Util.comp_effect_name uu____6446
                              in
                           ((let uu____6450 =
                               let uu____6452 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef
                                  in
                               Prims.op_Negation uu____6452  in
                             if uu____6450
                             then
                               let uu____6455 =
                                 let uu____6461 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str
                                    in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____6461)
                                  in
                               FStar_Errors.raise_error uu____6455
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____6468 =
                                 FStar_Syntax_Syntax.lcomp_comp c  in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____6468 u_c
                                in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let c1 =
                               let uu____6505 =
                                 FStar_TypeChecker_Env.is_total_effect env1
                                   ef
                                  in
                               if uu____6505
                               then
                                 let uu____6508 =
                                   FStar_Syntax_Syntax.mk_Total repr  in
                                 FStar_All.pipe_right uu____6508
                                   FStar_Syntax_Util.lcomp_of_comp
                               else
                                 (let ct =
                                    {
                                      FStar_Syntax_Syntax.comp_univs = [u_c];
                                      FStar_Syntax_Syntax.effect_name =
                                        FStar_Parser_Const.effect_Dv_lid;
                                      FStar_Syntax_Syntax.result_typ = repr;
                                      FStar_Syntax_Syntax.effect_args = [];
                                      FStar_Syntax_Syntax.flags = []
                                    }  in
                                  let uu____6520 =
                                    FStar_Syntax_Syntax.mk_Comp ct  in
                                  FStar_All.pipe_right uu____6520
                                    FStar_Syntax_Util.lcomp_of_comp)
                                in
                             let uu____6521 =
                               comp_check_expected_typ env1 e3 c1  in
                             match uu____6521 with
                             | (e4,c2,g') ->
                                 let uu____6537 =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 (e4, c2, uu____6537)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6539;
              FStar_Syntax_Syntax.vars = uu____6540;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6588 =
               let uu____6590 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6590  in
             if uu____6588
             then
               let uu____6593 =
                 let uu____6599 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6599)  in
               FStar_Errors.raise_error uu____6593 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6605 = FStar_Syntax_Util.head_and_args top  in
             match uu____6605 with
             | (reflect_op,uu____6629) ->
                 let uu____6654 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6654 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6694 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6694 with
                       | (env_no_ex,topt) ->
                           let uu____6713 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____6733 =
                                 let uu____6740 =
                                   let uu____6741 =
                                     let uu____6758 =
                                       let uu____6769 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6778 =
                                         let uu____6789 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6789]  in
                                       uu____6769 :: uu____6778  in
                                     (repr, uu____6758)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6741  in
                                 FStar_Syntax_Syntax.mk uu____6740  in
                               uu____6733 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6834 =
                               let uu____6841 =
                                 let uu____6842 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6842
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6841 t  in
                             match uu____6834 with
                             | (t1,uu____6868,g) ->
                                 let uu____6870 =
                                   let uu____6871 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____6871.FStar_Syntax_Syntax.n  in
                                 (match uu____6870 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____6884,(res,uu____6886)::(wp,uu____6888)::[])
                                      -> (t1, res, wp, g)
                                  | uu____6945 -> failwith "Impossible")
                              in
                           (match uu____6713 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____6971 =
                                  let uu____6978 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____6978 with
                                  | (e2,c,g) ->
                                      ((let uu____6995 =
                                          let uu____6997 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____6997
                                           in
                                        if uu____6995
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7020 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7020 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7031 =
                                                let uu____7041 =
                                                  let uu____7049 =
                                                    let uu____7051 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7053 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7051 uu____7053
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7049,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7041]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7031);
                                             (let uu____7071 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7071)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7075 =
                                              let uu____7076 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7076
                                               in
                                            (e2, uu____7075)))
                                   in
                                (match uu____6971 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7092 =
                                         let uu____7093 =
                                           let uu____7094 =
                                             let uu____7095 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7095]  in
                                           let uu____7096 =
                                             let uu____7107 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7107]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7094;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7096;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7093
                                          in
                                       FStar_All.pipe_right uu____7092
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7167 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7167 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_Syntax_Syntax.eff_name),
                                                        (c1.FStar_Syntax_Syntax.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____7190 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7190))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7229 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7229 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7279,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7280))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7333 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7333 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7408 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7618 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7408 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7737 =
               let uu____7738 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7738 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7737 instantiate_both  in
           ((let uu____7754 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7754
             then
               let uu____7757 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7759 = FStar_Syntax_Print.term_to_string top  in
               let uu____7761 =
                 let uu____7763 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7763
                   (fun uu___3_7770  ->
                      match uu___3_7770 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7757
                 uu____7759 uu____7761
             else ());
            (let uu____7779 = tc_term (no_inst env2) head1  in
             match uu____7779 with
             | (head2,chead,g_head) ->
                 let uu____7795 =
                   let uu____7802 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____7805 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____7805))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____7802
                   then
                     let uu____7814 =
                       let uu____7821 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____7821
                        in
                     match uu____7814 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____7835 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____7835)
                    in
                 (match uu____7795 with
                  | (e1,c,g) ->
                      let uu____7847 =
                        let uu____7854 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____7854
                        then
                          let uu____7863 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____7863 with
                          | (e2,res_typ,implicits) ->
                              let uu____7879 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____7879, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____7847 with
                       | (e2,c1,implicits) ->
                           ((let uu____7892 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____7892
                             then
                               let uu____7895 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____7895
                             else ());
                            (let uu____7900 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____7900 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____7919 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____7919
                                   then
                                     let uu____7922 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____7924 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____7922 uu____7924
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____7967 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____7967 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____7987 = tc_term env12 e1  in
                (match uu____7987 with
                 | (e11,c1,g1) ->
                     let uu____8003 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8017 = FStar_Syntax_Util.type_u ()  in
                           (match uu____8017 with
                            | (k,uu____8029) ->
                                let uu____8030 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8030 with
                                 | (res_t,uu____8051,g) ->
                                     let uu____8065 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8066 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8065, res_t, uu____8066)))
                        in
                     (match uu____8003 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8077 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8077
                            then
                              let uu____8080 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8080
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____8207 =
                              let uu____8212 =
                                FStar_List.fold_right
                                  (fun uu____8294  ->
                                     fun uu____8295  ->
                                       match (uu____8294, uu____8295) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____8540 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8540)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____8212 with
                              | (cases,g) ->
                                  let uu____8645 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8645, g)
                               in
                            match uu____8207 with
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
                                           (fun uu____8787  ->
                                              match uu____8787 with
                                              | ((pat,wopt,br),uu____8832,eff_label,uu____8834,uu____8835,uu____8836)
                                                  ->
                                                  let uu____8873 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____8873)))
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
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____8940 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____8940
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____8948 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____8948  in
                                     let lb =
                                       let uu____8952 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____8952 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____8958 =
                                         let uu____8965 =
                                           let uu____8966 =
                                             let uu____8980 =
                                               let uu____8983 =
                                                 let uu____8984 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____8984]  in
                                               FStar_Syntax_Subst.close
                                                 uu____8983 e_match
                                                in
                                             ((false, [lb]), uu____8980)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____8966
                                            in
                                         FStar_Syntax_Syntax.mk uu____8965
                                          in
                                       uu____8958
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____9017 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____9017
                                  then
                                    let uu____9020 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9022 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____9020 uu____9022
                                  else ());
                                 (let uu____9027 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____9027))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9028;
                FStar_Syntax_Syntax.lbunivs = uu____9029;
                FStar_Syntax_Syntax.lbtyp = uu____9030;
                FStar_Syntax_Syntax.lbeff = uu____9031;
                FStar_Syntax_Syntax.lbdef = uu____9032;
                FStar_Syntax_Syntax.lbattrs = uu____9033;
                FStar_Syntax_Syntax.lbpos = uu____9034;_}::[]),uu____9035)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9061),uu____9062) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9080;
                FStar_Syntax_Syntax.lbunivs = uu____9081;
                FStar_Syntax_Syntax.lbtyp = uu____9082;
                FStar_Syntax_Syntax.lbeff = uu____9083;
                FStar_Syntax_Syntax.lbdef = uu____9084;
                FStar_Syntax_Syntax.lbattrs = uu____9085;
                FStar_Syntax_Syntax.lbpos = uu____9086;_}::uu____9087),uu____9088)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9116),uu____9117) ->
           check_inner_let_rec env1 top)

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun head1  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____9151 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9190))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9231 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9151 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9264 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9264 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9268 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9268)
                 in
              let uu____9271 =
                let uu____9278 =
                  let uu____9279 =
                    let uu____9280 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9280
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9279  in
                tc_term uu____9278 typ  in
              (match uu____9271 with
               | (typ1,uu____9296,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9299 = tc_tactic env tau  in
                     match uu____9299 with
                     | (tau1,uu____9313,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1196_9318 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1196_9318.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1196_9318.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9320 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9320
                            then
                              let uu____9325 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9325
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9331 =
                              let uu____9332 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_Syntax_Util.lcomp_of_comp uu____9332
                               in
                            (t, uu____9331,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___1204_9336 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1204_9336.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1204_9336.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1204_9336.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1204_9336.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1204_9336.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1204_9336.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1204_9336.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1204_9336.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1204_9336.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1204_9336.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1204_9336.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1204_9336.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1204_9336.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1204_9336.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1204_9336.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1204_9336.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1204_9336.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1204_9336.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1204_9336.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1204_9336.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1204_9336.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1204_9336.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1204_9336.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1204_9336.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1204_9336.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1204_9336.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1204_9336.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1204_9336.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1204_9336.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1204_9336.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1204_9336.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1204_9336.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1204_9336.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1204_9336.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1204_9336.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1204_9336.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1204_9336.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1204_9336.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1204_9336.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1204_9336.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1204_9336.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1204_9336.FStar_TypeChecker_Env.nbe)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____9359 = tc_tactic env tactic  in
          (match uu____9359 with
           | (tactic1,uu____9373,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____9425 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9425 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9446 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9446
              then FStar_Util.Inl t
              else
                (let uu____9455 =
                   let uu____9456 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____9456
                    in
                 FStar_Util.Inr uu____9455)
               in
            let is_data_ctor uu___4_9465 =
              match uu___4_9465 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9470) -> true
              | uu____9478 -> false  in
            let uu____9482 =
              (is_data_ctor dc) &&
                (let uu____9485 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9485)
               in
            if uu____9482
            then
              let uu____9494 =
                let uu____9500 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9500)  in
              let uu____9504 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9494 uu____9504
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9522 =
            let uu____9524 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9524
             in
          failwith uu____9522
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9551 =
            let uu____9556 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9556  in
          value_check_expected_typ env1 e uu____9551
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9558 =
            let uu____9571 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9571 with
            | FStar_Pervasives_Native.None  ->
                let uu____9586 = FStar_Syntax_Util.type_u ()  in
                (match uu____9586 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9558 with
           | (t,uu____9624,g0) ->
               let uu____9638 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____9638 with
                | (e1,uu____9659,g1) ->
                    let uu____9673 =
                      let uu____9674 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9674
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____9675 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9673, uu____9675)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9677 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9687 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9687)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9677 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1269_9701 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1269_9701.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1269_9701.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9704 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9704 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9725 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9725
                       then FStar_Util.Inl t1
                       else
                         (let uu____9734 =
                            let uu____9735 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____9735
                             in
                          FStar_Util.Inr uu____9734)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9737;
             FStar_Syntax_Syntax.vars = uu____9738;_},uu____9739)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9744 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9744
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9754 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9754
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9764;
             FStar_Syntax_Syntax.vars = uu____9765;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____9774 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9774 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9798 =
                     let uu____9804 =
                       let uu____9806 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____9808 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____9810 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9806 uu____9808 uu____9810
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9804)
                      in
                   let uu____9814 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____9798 uu____9814)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9831 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9836 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9836 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9838 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9838 with
           | ((us,t),range) ->
               ((let uu____9861 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____9861
                 then
                   let uu____9866 =
                     let uu____9868 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____9868  in
                   let uu____9869 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____9871 = FStar_Range.string_of_range range  in
                   let uu____9873 = FStar_Range.string_of_use_range range  in
                   let uu____9875 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____9866 uu____9869 uu____9871 uu____9873 uu____9875
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9883 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9883 us  in
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
          let uu____9911 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9911 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____9925 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9925 with
                | (env2,uu____9939) ->
                    let uu____9944 = tc_binders env2 bs1  in
                    (match uu____9944 with
                     | (bs2,env3,g,us) ->
                         let uu____9963 = tc_comp env3 c1  in
                         (match uu____9963 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1349_9982 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1349_9982.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1349_9982.FStar_Syntax_Syntax.vars)
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
                                  let uu____9993 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____9993
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
          let uu____10009 =
            let uu____10014 =
              let uu____10015 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10015]  in
            FStar_Syntax_Subst.open_term uu____10014 phi  in
          (match uu____10009 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10043 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10043 with
                | (env2,uu____10057) ->
                    let uu____10062 =
                      let uu____10077 = FStar_List.hd x1  in
                      tc_binder env2 uu____10077  in
                    (match uu____10062 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10113 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10113
                           then
                             let uu____10116 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10118 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10120 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10116 uu____10118 uu____10120
                           else ());
                          (let uu____10127 = FStar_Syntax_Util.type_u ()  in
                           match uu____10127 with
                           | (t_phi,uu____10139) ->
                               let uu____10140 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10140 with
                                | (phi2,uu____10154,f2) ->
                                    let e1 =
                                      let uu___1387_10159 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1387_10159.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1387_10159.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10168 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10168
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10196) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10223 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10223
            then
              let uu____10226 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1400_10230 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1400_10230.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1400_10230.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10226
            else ());
           (let uu____10246 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10246 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10259 ->
          let uu____10260 =
            let uu____10262 = FStar_Syntax_Print.term_to_string top  in
            let uu____10264 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10262
              uu____10264
             in
          failwith uu____10260

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10276 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10278,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10291,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____10309 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10315 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10317 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10318 ->
            let uu____10320 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10320 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10325 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10326 =
              let uu____10332 =
                let uu____10334 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10334
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10332)  in
            FStar_Errors.raise_error uu____10326 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10338 =
              let uu____10344 =
                let uu____10346 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10346
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10344)  in
            FStar_Errors.raise_error uu____10338 r
        | FStar_Const.Const_reify  ->
            let uu____10350 =
              let uu____10356 =
                let uu____10358 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10358
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10356)  in
            FStar_Errors.raise_error uu____10350 r
        | FStar_Const.Const_reflect uu____10362 ->
            let uu____10363 =
              let uu____10369 =
                let uu____10371 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10371
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10369)  in
            FStar_Errors.raise_error uu____10363 r
        | uu____10375 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____10394) ->
          let uu____10403 = FStar_Syntax_Util.type_u ()  in
          (match uu____10403 with
           | (k,u) ->
               let uu____10416 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10416 with
                | (t1,uu____10430,g) ->
                    let uu____10432 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10432, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10434) ->
          let uu____10443 = FStar_Syntax_Util.type_u ()  in
          (match uu____10443 with
           | (k,u) ->
               let uu____10456 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10456 with
                | (t1,uu____10470,g) ->
                    let uu____10472 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10472, u, g)))
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
            let uu____10482 =
              let uu____10487 =
                let uu____10488 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10488 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10487  in
            uu____10482 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10505 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10505 with
           | (tc1,uu____10519,f) ->
               let uu____10521 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10521 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10571 =
                        let uu____10572 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10572.FStar_Syntax_Syntax.n  in
                      match uu____10571 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10575,us) -> us
                      | uu____10581 -> []  in
                    let uu____10582 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10582 with
                     | (uu____10605,args1) ->
                         let uu____10631 =
                           let uu____10654 = FStar_List.hd args1  in
                           let uu____10671 = FStar_List.tl args1  in
                           (uu____10654, uu____10671)  in
                         (match uu____10631 with
                          | (res,args2) ->
                              let uu____10752 =
                                let uu____10761 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10789  ->
                                          match uu___5_10789 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10797 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____10797 with
                                               | (env1,uu____10809) ->
                                                   let uu____10814 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____10814 with
                                                    | (e1,uu____10826,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____10761
                                  FStar_List.unzip
                                 in
                              (match uu____10752 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1529_10867 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1529_10867.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1529_10867.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____10873 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____10873))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____10883 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____10887 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____10897 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____10897
        | FStar_Syntax_Syntax.U_max us ->
            let uu____10901 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____10901
        | FStar_Syntax_Syntax.U_name x ->
            let uu____10905 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____10905
            then u2
            else
              (let uu____10910 =
                 let uu____10912 =
                   let uu____10914 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____10914 " not found"  in
                 Prims.op_Hat "Universe variable " uu____10912  in
               failwith uu____10910)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____10921 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____10921 FStar_Pervasives_Native.snd
         | uu____10930 -> aux u)

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail1 msg t =
            let uu____10961 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____10961 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11050 bs2 bs_expected1 =
              match uu____11050 with
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
                              uu____11241),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11242)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11257),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11258)) -> true
                           | uu____11267 -> false  in
                         let uu____11277 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11280 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11280 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11277
                         then
                           let uu____11282 =
                             let uu____11288 =
                               let uu____11290 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11290
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11288)
                              in
                           let uu____11294 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11282 uu____11294
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11298 =
                           let uu____11305 =
                             let uu____11306 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11306.FStar_Syntax_Syntax.n  in
                           match uu____11305 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11317 ->
                               ((let uu____11319 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11319
                                 then
                                   let uu____11322 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11322
                                 else ());
                                (let uu____11327 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11327 with
                                 | (t,uu____11341,g1_env) ->
                                     let g2_env =
                                       let uu____11344 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11344
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11349 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11349 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11352 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11358 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11352 uu____11358
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____11360 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____11360
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11362 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11362)))
                            in
                         match uu____11298 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1627_11388 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1627_11388.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1627_11388.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11411 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11411
                                in
                             let uu____11414 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11414 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11479 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11479,
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
                  | uu____11651 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11661 = tc_binders env1 bs  in
                  match uu____11661 with
                  | (bs1,envbody,g_env,uu____11691) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____11747 =
                    let uu____11748 = FStar_Syntax_Subst.compress t2  in
                    uu____11748.FStar_Syntax_Syntax.n  in
                  match uu____11747 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11781 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11801 -> failwith "Impossible");
                       (let uu____11811 = tc_binders env1 bs  in
                        match uu____11811 with
                        | (bs1,envbody,g_env,uu____11853) ->
                            let uu____11854 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____11854 with
                             | (envbody1,uu____11892) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____11913;
                         FStar_Syntax_Syntax.pos = uu____11914;
                         FStar_Syntax_Syntax.vars = uu____11915;_},uu____11916)
                      ->
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
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12073) ->
                      let uu____12078 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12078 with
                       | (uu____12139,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12216 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12216 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12361 c_expected2
                               body3 =
                               match uu____12361 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12475 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12475,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12492 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12492
                                           in
                                        let uu____12493 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12493,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12510 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12510
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
                                               let uu____12576 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12576 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12603 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12603 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12658 =
                                                           let uu____12685 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12685,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12658
                                                           c_expected4 body3))
                                           | uu____12708 ->
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
                             let uu____12737 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____12737 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1753_12802 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1753_12802.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1753_12802.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1753_12802.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1753_12802.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1753_12802.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1753_12802.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1753_12802.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1753_12802.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1753_12802.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1753_12802.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1753_12802.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1753_12802.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1753_12802.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1753_12802.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1753_12802.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1753_12802.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1753_12802.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1753_12802.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1753_12802.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1753_12802.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1753_12802.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1753_12802.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1753_12802.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1753_12802.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1753_12802.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1753_12802.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1753_12802.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1753_12802.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1753_12802.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1753_12802.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1753_12802.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1753_12802.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1753_12802.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1753_12802.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1753_12802.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1753_12802.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1753_12802.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1753_12802.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1753_12802.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1753_12802.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1753_12802.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1753_12802.FStar_TypeChecker_Env.nbe)
                               }  in
                             let uu____12809 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____12875  ->
                                       fun uu____12876  ->
                                         match (uu____12875, uu____12876)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____12967 =
                                               let uu____12974 =
                                                 let uu____12975 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____12975
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____12974 t3  in
                                             (match uu____12967 with
                                              | (t4,uu____12999,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____13012 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1771_13015
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1771_13015.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1771_13015.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____13012 ::
                                                          letrec_binders
                                                    | uu____13016 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13021 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13021)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____12809 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13041 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13041)
                              in
                           let uu____13044 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13044 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13120 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13120 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13167 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13167))))
                  | uu____13184 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13216 =
                          let uu____13217 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____13217
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____13216
                      else
                        (let uu____13221 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13221 with
                         | (uu____13270,bs1,uu____13272,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13304 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13304 with
          | (env1,topt) ->
              ((let uu____13324 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13324
                then
                  let uu____13327 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13327
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13341 = expected_function_typ1 env1 topt body  in
                match uu____13341 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13382 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____13382
                      then
                        let uu____13385 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____13390 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____13395 =
                          let uu____13397 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____13397 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13385 uu____13390 uu____13395
                      else ());
                     (let uu____13407 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13407
                      then
                        let uu____13412 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13415 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13412 uu____13415
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13421 =
                        let should_check_expected_effect =
                          let uu____13434 =
                            let uu____13441 =
                              let uu____13442 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13442.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13441)  in
                          match uu____13434 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13448,(FStar_Util.Inr
                                           expected_c,uu____13450),uu____13451))
                              -> false
                          | uu____13501 -> true  in
                        let uu____13509 =
                          tc_term
                            (let uu___1844_13518 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1844_13518.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1844_13518.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1844_13518.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1844_13518.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1844_13518.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1844_13518.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1844_13518.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1844_13518.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1844_13518.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1844_13518.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1844_13518.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1844_13518.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1844_13518.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1844_13518.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1844_13518.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1844_13518.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1844_13518.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1844_13518.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1844_13518.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1844_13518.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1844_13518.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1844_13518.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1844_13518.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1844_13518.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1844_13518.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1844_13518.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1844_13518.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1844_13518.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1844_13518.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1844_13518.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1844_13518.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1844_13518.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1844_13518.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1844_13518.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1844_13518.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1844_13518.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1844_13518.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1844_13518.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1844_13518.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1844_13518.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1844_13518.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____13509 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13545 =
                                let uu____13552 =
                                  let uu____13557 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____13557)  in
                                check_expected_effect
                                  (let uu___1852_13560 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___1852_13560.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___1852_13560.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___1852_13560.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___1852_13560.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___1852_13560.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___1852_13560.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___1852_13560.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___1852_13560.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___1852_13560.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___1852_13560.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___1852_13560.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___1852_13560.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___1852_13560.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___1852_13560.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___1852_13560.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___1852_13560.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___1852_13560.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___1852_13560.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___1852_13560.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___1852_13560.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___1852_13560.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___1852_13560.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___1852_13560.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___1852_13560.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___1852_13560.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___1852_13560.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___1852_13560.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___1852_13560.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___1852_13560.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___1852_13560.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___1852_13560.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___1852_13560.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___1852_13560.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___1852_13560.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___1852_13560.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___1852_13560.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___1852_13560.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___1852_13560.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___1852_13560.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___1852_13560.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___1852_13560.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___1852_13560.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____13552
                                 in
                              (match uu____13545 with
                               | (body3,cbody1,guard) ->
                                   let uu____13574 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____13574))
                            else
                              (let uu____13581 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____13581, guard_body1))
                         in
                      match uu____13421 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13606 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13609 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13609)
                               in
                            if uu____13606
                            then
                              let uu____13612 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13613 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13612
                                uu____13613
                            else
                              (let guard =
                                 let uu____13617 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13617
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
                          let uu____13631 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13652
                                     -> (e, t1, guard1)
                                 | uu____13667 ->
                                     let uu____13668 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13668 with
                                      | (e1,guard') ->
                                          let uu____13681 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____13681)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13631 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13692 =
                                 let uu____13697 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13697 guard2
                                  in
                               (match uu____13692 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____13746 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____13746
               then
                 let uu____13749 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____13751 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13749
                   uu____13751
               else ());
              (let monadic_application uu____13829 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____13829 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____13890 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____13890 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___1912_13904 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___1912_13904.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___1912_13904.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___1912_13904.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____13905 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____13921 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____13921
                                   in
                                (cres1, g)
                            | uu____13922 ->
                                let g =
                                  let uu____13932 =
                                    let uu____13933 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____13933
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____13932
                                   in
                                let uu____13934 =
                                  let uu____13935 =
                                    let uu____13936 =
                                      let uu____13937 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____13937
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____13936
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____13935
                                   in
                                (uu____13934, g)
                             in
                          (match uu____13905 with
                           | (cres2,guard1) ->
                               ((let uu____13949 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____13949
                                 then
                                   let uu____13952 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____13952
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____13972  ->
                                             match uu____13972 with
                                             | (uu____13982,uu____13983,lc)
                                                 ->
                                                 (let uu____13991 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____13991)
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
                                   let uu____14004 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____14004
                                   then
                                     ((let uu____14008 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____14008
                                       then
                                         let uu____14011 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____14011
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____14019 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____14019
                                       then
                                         let uu____14022 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____14022
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____14053  ->
                                          match uu____14053 with
                                          | ((e,q),x,c) ->
                                              ((let uu____14095 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14095
                                                then
                                                  let uu____14098 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____14103 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14105 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____14098 uu____14103
                                                    uu____14105
                                                else ());
                                               (let uu____14110 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14110
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
                                                    c (x, out_c)))) cres3
                                     arg_comps_rev
                                    in
                                 let comp1 =
                                   (let uu____14121 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____14121
                                    then
                                      let uu____14124 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____14124
                                    else ());
                                   (let uu____14129 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____14129
                                    then
                                      FStar_TypeChecker_Util.bind
                                        head2.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some head2)
                                        chead1
                                        (FStar_Pervasives_Native.None, comp)
                                    else
                                      FStar_TypeChecker_Util.bind
                                        head2.FStar_Syntax_Syntax.pos env
                                        FStar_Pervasives_Native.None chead1
                                        (FStar_Pervasives_Native.None, comp))
                                    in
                                 let comp2 =
                                   FStar_TypeChecker_Util.subst_lcomp subst1
                                     comp1
                                    in
                                 let shortcuts_evaluation_order =
                                   let uu____14141 =
                                     let uu____14142 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____14142.FStar_Syntax_Syntax.n  in
                                   match uu____14141 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____14147 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____14170  ->
                                              match uu____14170 with
                                              | (arg,uu____14184,uu____14185)
                                                  -> arg :: args1) []
                                         arg_comps_rev
                                        in
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head2
                                         args1 FStar_Pervasives_Native.None r
                                        in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.res_typ
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic env
                                       app1
                                       comp2.FStar_Syntax_Syntax.eff_name
                                       comp2.FStar_Syntax_Syntax.res_typ
                                   else
                                     (let uu____14196 =
                                        let map_fun uu____14262 =
                                          match uu____14262 with
                                          | ((e,q),uu____14303,c) ->
                                              ((let uu____14326 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14326
                                                then
                                                  let uu____14329 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14331 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____14329 uu____14331
                                                else ());
                                               (let uu____14336 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14336
                                                then
                                                  ((let uu____14362 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14362
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  (let warn_effectful_args =
                                                     (FStar_TypeChecker_Util.must_erase_for_extraction
                                                        env
                                                        chead1.FStar_Syntax_Syntax.res_typ)
                                                       &&
                                                       (let uu____14403 =
                                                          let uu____14405 =
                                                            let uu____14406 =
                                                              FStar_Syntax_Util.un_uinst
                                                                head2
                                                               in
                                                            uu____14406.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____14405
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let uu____14411
                                                                =
                                                                FStar_Parser_Const.psconst
                                                                  "ignore"
                                                                 in
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv
                                                                uu____14411
                                                          | uu____14413 ->
                                                              true
                                                           in
                                                        Prims.op_Negation
                                                          uu____14403)
                                                      in
                                                   if warn_effectful_args
                                                   then
                                                     (let uu____14417 =
                                                        let uu____14423 =
                                                          let uu____14425 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e
                                                             in
                                                          let uu____14427 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head2
                                                             in
                                                          FStar_Util.format3
                                                            "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                            uu____14425
                                                            (c.FStar_Syntax_Syntax.eff_name).FStar_Ident.str
                                                            uu____14427
                                                           in
                                                        (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                          uu____14423)
                                                         in
                                                      FStar_Errors.log_issue
                                                        e.FStar_Syntax_Syntax.pos
                                                        uu____14417)
                                                   else ();
                                                   (let uu____14434 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14434
                                                    then
                                                      FStar_Util.print_string
                                                        "... lifting!\n"
                                                    else ());
                                                   (let x =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    let e1 =
                                                      FStar_TypeChecker_Util.maybe_lift
                                                        env e
                                                        c.FStar_Syntax_Syntax.eff_name
                                                        comp2.FStar_Syntax_Syntax.eff_name
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    let uu____14442 =
                                                      let uu____14451 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____14451, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____14442)))))
                                           in
                                        let uu____14480 =
                                          let uu____14511 =
                                            let uu____14540 =
                                              let uu____14551 =
                                                let uu____14560 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____14560,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____14551 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____14540
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____14511
                                           in
                                        match uu____14480 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____14761 =
                                              let uu____14762 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____14762
                                               in
                                            let uu____14783 =
                                              let uu____14784 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____14784  in
                                            (lifted_args, uu____14761,
                                              uu____14783)
                                         in
                                      match uu____14196 with
                                      | (lifted_args,head3,args1) ->
                                          let app =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head3 args1
                                              FStar_Pervasives_Native.None r
                                             in
                                          let app1 =
                                            FStar_TypeChecker_Util.maybe_lift
                                              env app
                                              cres3.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ
                                             in
                                          let app2 =
                                            FStar_TypeChecker_Util.maybe_monadic
                                              env app1
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ
                                             in
                                          let bind_lifted_args e uu___6_14895
                                            =
                                            match uu___6_14895 with
                                            | FStar_Pervasives_Native.None 
                                                -> e
                                            | FStar_Pervasives_Native.Some
                                                (x,m,t,e1) ->
                                                let lb =
                                                  FStar_Syntax_Util.mk_letbinding
                                                    (FStar_Util.Inl x) [] t m
                                                    e1 []
                                                    e1.FStar_Syntax_Syntax.pos
                                                   in
                                                let letbinding =
                                                  let uu____14956 =
                                                    let uu____14963 =
                                                      let uu____14964 =
                                                        let uu____14978 =
                                                          let uu____14981 =
                                                            let uu____14982 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____14982]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____14981 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____14978)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____14964
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____14963
                                                     in
                                                  uu____14956
                                                    FStar_Pervasives_Native.None
                                                    e.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_meta
                                                     (letbinding,
                                                       (FStar_Syntax_Syntax.Meta_monadic
                                                          (m,
                                                            (comp2.FStar_Syntax_Syntax.res_typ)))))
                                                  FStar_Pervasives_Native.None
                                                  e.FStar_Syntax_Syntax.pos
                                             in
                                          FStar_List.fold_left
                                            bind_lifted_args app2 lifted_args)
                                    in
                                 let uu____15034 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____15034 with
                                 | (comp3,g) ->
                                     ((let uu____15052 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____15052
                                       then
                                         let uu____15055 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____15057 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____15055 uu____15057
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____15138 bs args1 =
                 match uu____15138 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15277))::rest,
                         (uu____15279,FStar_Pervasives_Native.None )::uu____15280)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15341 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15341 with
                           | (t1,g_ex) ->
                               let uu____15354 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15354 with
                                | (varg,uu____15375,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15403 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15403)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15412 =
                                      let uu____15447 =
                                        let uu____15458 =
                                          let uu____15467 =
                                            let uu____15468 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15468
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15467)
                                           in
                                        uu____15458 :: outargs  in
                                      (subst2, uu____15447, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15412 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15514,FStar_Pervasives_Native.None
                                                                 )::uu____15515)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15577 = tc_tactic env tau1  in
                          (match uu____15577 with
                           | (tau2,uu____15591,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15594 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15594 with
                                | (t1,g_ex) ->
                                    let uu____15607 =
                                      let uu____15620 =
                                        let uu____15627 =
                                          let uu____15632 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15632, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15627
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15620
                                       in
                                    (match uu____15607 with
                                     | (varg,uu____15645,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15673 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15673)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____15682 =
                                           let uu____15717 =
                                             let uu____15728 =
                                               let uu____15737 =
                                                 let uu____15738 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____15738
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15737)
                                                in
                                             uu____15728 :: outargs  in
                                           (subst2, uu____15717, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____15682 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____15854,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15855)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____15866),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15867)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____15875),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15876)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____15891 ->
                                let uu____15900 =
                                  let uu____15906 =
                                    let uu____15908 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____15910 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____15912 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____15914 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____15908 uu____15910 uu____15912
                                      uu____15914
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____15906)
                                   in
                                FStar_Errors.raise_error uu____15900
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2122_15921 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2122_15921.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2122_15921.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____15923 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____15923
                             then
                               let uu____15926 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____15928 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15930 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15932 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____15934 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____15926 uu____15928 uu____15930
                                 uu____15932 uu____15934
                             else ());
                            (let uu____15939 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____15939 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2131_15954 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2131_15954.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2131_15954.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2131_15954.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2131_15954.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2131_15954.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2131_15954.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2131_15954.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2131_15954.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2131_15954.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2131_15954.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2131_15954.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2131_15954.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2131_15954.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2131_15954.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2131_15954.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2131_15954.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2131_15954.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2131_15954.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2131_15954.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2131_15954.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2131_15954.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2131_15954.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2131_15954.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2131_15954.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2131_15954.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2131_15954.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2131_15954.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2131_15954.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2131_15954.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2131_15954.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2131_15954.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2131_15954.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2131_15954.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2131_15954.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2131_15954.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2131_15954.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2131_15954.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2131_15954.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2131_15954.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2131_15954.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2131_15954.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2131_15954.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____15956 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____15956
                                   then
                                     let uu____15959 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____15961 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____15963 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____15959 uu____15961 uu____15963
                                   else ());
                                  (let uu____15968 = tc_term env2 e  in
                                   match uu____15968 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____15985 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____15985
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____16008 =
                                           let uu____16011 =
                                             let uu____16020 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16020
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____16011
                                            in
                                         (uu____16008, aq)  in
                                       let uu____16029 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____16029
                                       then
                                         let subst2 =
                                           let uu____16039 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16039 e1
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
                      | (uu____16138,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16174) ->
                          let uu____16225 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16225 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____16281 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____16281
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____16312 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____16312 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____16334 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____16334)
                                             in
                                          ((let uu____16336 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____16336
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
                                 | uu____16383 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____16391 =
                                         let uu____16392 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____16392.FStar_Syntax_Syntax.n
                                          in
                                       match uu____16391 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____16395;
                                              FStar_Syntax_Syntax.index =
                                                uu____16396;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____16398)
                                           -> norm_tres tres4
                                       | uu____16406 -> tres3  in
                                     let uu____16407 = norm_tres tres1  in
                                     aux true solve ghead2 uu____16407
                                 | uu____16409 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____16412 ->
                                     let uu____16413 =
                                       let uu____16419 =
                                         let uu____16421 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____16423 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____16425 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____16421 uu____16423
                                           uu____16425
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____16419)
                                        in
                                     let uu____16429 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____16413
                                       uu____16429
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____16459 =
                   let uu____16460 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16460.FStar_Syntax_Syntax.n  in
                 match uu____16459 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16469 ->
                     let uu____16482 =
                       FStar_List.fold_right
                         (fun uu____16513  ->
                            fun uu____16514  ->
                              match uu____16514 with
                              | (bs,guard1) ->
                                  let uu____16541 =
                                    let uu____16554 =
                                      let uu____16555 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16555
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16554
                                     in
                                  (match uu____16541 with
                                   | (t,uu____16572,g) ->
                                       let uu____16586 =
                                         let uu____16589 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16589 :: bs  in
                                       let uu____16590 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16586, uu____16590))) args
                         ([], guard)
                        in
                     (match uu____16482 with
                      | (bs,guard1) ->
                          let uu____16607 =
                            let uu____16614 =
                              let uu____16627 =
                                let uu____16628 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16628
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16627
                               in
                            match uu____16614 with
                            | (t,uu____16645,g) ->
                                let uu____16659 = FStar_Options.ml_ish ()  in
                                if uu____16659
                                then
                                  let uu____16668 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16671 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16668, uu____16671)
                                else
                                  (let uu____16676 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16679 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16676, uu____16679))
                             in
                          (match uu____16607 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16698 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16698
                                 then
                                   let uu____16702 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16704 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16706 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16702 uu____16704 uu____16706
                                 else ());
                                (let g =
                                   let uu____16712 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16712
                                    in
                                 let uu____16713 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16713))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16714;
                        FStar_Syntax_Syntax.pos = uu____16715;
                        FStar_Syntax_Syntax.vars = uu____16716;_},uu____16717)
                     ->
                     let uu____16754 =
                       FStar_List.fold_right
                         (fun uu____16785  ->
                            fun uu____16786  ->
                              match uu____16786 with
                              | (bs,guard1) ->
                                  let uu____16813 =
                                    let uu____16826 =
                                      let uu____16827 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16827
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16826
                                     in
                                  (match uu____16813 with
                                   | (t,uu____16844,g) ->
                                       let uu____16858 =
                                         let uu____16861 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16861 :: bs  in
                                       let uu____16862 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16858, uu____16862))) args
                         ([], guard)
                        in
                     (match uu____16754 with
                      | (bs,guard1) ->
                          let uu____16879 =
                            let uu____16886 =
                              let uu____16899 =
                                let uu____16900 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16900
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16899
                               in
                            match uu____16886 with
                            | (t,uu____16917,g) ->
                                let uu____16931 = FStar_Options.ml_ish ()  in
                                if uu____16931
                                then
                                  let uu____16940 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16943 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16940, uu____16943)
                                else
                                  (let uu____16948 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16951 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16948, uu____16951))
                             in
                          (match uu____16879 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16970 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16970
                                 then
                                   let uu____16974 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16976 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16978 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16974 uu____16976 uu____16978
                                 else ());
                                (let g =
                                   let uu____16984 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16984
                                    in
                                 let uu____16985 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16985))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____17008 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____17008 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____17030 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____17030)  in
                          ((let uu____17032 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17032
                            then
                              let uu____17035 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17037 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17039 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17042 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17035 uu____17037 uu____17039
                                uu____17042
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17088) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17094,uu____17095) ->
                     check_function_app t guard
                 | uu____17136 ->
                     let uu____17137 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17137
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____17220 =
                    FStar_List.fold_left2
                      (fun uu____17289  ->
                         fun uu____17290  ->
                           fun uu____17291  ->
                             match (uu____17289, uu____17290, uu____17291)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17444 =
                                     let uu____17446 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17446 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17444
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17452 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17452 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17481 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17481 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17486 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17486)
                                              &&
                                              (let uu____17489 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____17489))
                                          in
                                       let uu____17491 =
                                         let uu____17502 =
                                           let uu____17513 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17513]  in
                                         FStar_List.append seen uu____17502
                                          in
                                       let uu____17546 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17491, uu____17546, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17220 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17614 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17614
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____17617 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17617 with | (c2,g) -> (e, c2, g)))
              | uu____17634 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
          FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
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
            let uu____17725 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17725 with
            | (head1,args) ->
                let uu____17768 =
                  let uu____17769 = FStar_Syntax_Subst.compress head1  in
                  uu____17769.FStar_Syntax_Syntax.n  in
                (match uu____17768 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____17773;
                        FStar_Syntax_Syntax.vars = uu____17774;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____17781 ->
                     if norm1
                     then t1
                     else
                       (let uu____17785 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____17785))
          
          and unfold_once t f us args =
            let uu____17803 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____17803
            then t
            else
              (let uu____17808 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____17808 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____17828 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____17828 with
                    | (uu____17833,head_def) ->
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
          let uu____17840 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____17840  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____17859 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____17859
           then
             let uu____17864 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____17866 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____17864 uu____17866
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____17886 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____17888 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____17886 uu____17888 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____17892 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____17892 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____17936 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____17936 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____17937;
                    FStar_Syntax_Syntax.pos = uu____17938;
                    FStar_Syntax_Syntax.vars = uu____17939;_} ->
                    let uu____17942 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____17942 with
                     | (head_p,args_p) ->
                         let uu____17985 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____17985
                         then
                           let uu____17988 =
                             let uu____17989 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____17989.FStar_Syntax_Syntax.n  in
                           (match uu____17988 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____17994 =
                                    let uu____17996 =
                                      let uu____17998 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____17998
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____17996
                                     in
                                  if uu____17994
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____18026 =
                                    let uu____18051 =
                                      let uu____18055 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18055
                                       in
                                    match uu____18051 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18104 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18104 with
                                         | (params_p,uu____18162) ->
                                             let uu____18203 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18203 with
                                              | (params_s,uu____18261) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____18026 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18390  ->
                                             fun uu____18391  ->
                                               match (uu____18390,
                                                       uu____18391)
                                               with
                                               | ((p,uu____18425),(s,uu____18427))
                                                   ->
                                                   let uu____18460 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18460 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18463 =
                                                          let uu____18465 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18467 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18465
                                                            uu____18467
                                                           in
                                                        fail2 uu____18463
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
                            | uu____18472 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18476 =
                              let uu____18478 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18480 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18478 uu____18480
                               in
                            fail2 uu____18476))
                | uu____18483 ->
                    let uu____18484 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18484 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18521 = FStar_Syntax_Util.head_and_args e  in
          match uu____18521 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18585 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18585 with
                    | (us,t_f) ->
                        let uu____18602 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18602 with
                         | (formals,t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18731 formals1 args1 =
                                 match uu____18731 with
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
                                          let uu____18876 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____18876, bvs, guard)
                                      | ((f1,uu____18882)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____18940 =
                                            let uu____18961 =
                                              let uu____18962 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____18962.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18961 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2431_18987 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2431_18987.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2431_18987.FStar_Syntax_Syntax.index);
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
                                                uu____19010 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____19024 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____19024 with
                                                 | (a1,uu____19052,g) ->
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
                                            | uu____19076 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____18940 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19138 =
                                                 let uu____19161 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19161)
                                                  in
                                               aux uu____19138 formals2 args2)
                                      | uu____19200 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19256 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19305 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19305
           then
             let uu____19310 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19312 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19310
               uu____19312
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19327 ->
               let uu____19334 =
                 let uu____19336 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19336
                  in
               failwith uu____19334
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2463_19351 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2463_19351.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2463_19351.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19352 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19352,
                 (let uu___2466_19356 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2466_19356.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2470_19359 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2470_19359.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2470_19359.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19360 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19360,
                 (let uu___2473_19364 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2473_19364.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19365 ->
               let uu____19366 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19366 with
                | (uu____19388,e_c,uu____19390,uu____19391) ->
                    let uu____19396 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19396 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____19419 =
                              let uu____19421 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t
                                 in
                              Prims.op_Negation uu____19421  in
                            if uu____19419
                            then
                              let uu____19424 =
                                let uu____19426 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____19428 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19426 uu____19428
                                 in
                              fail1 uu____19424
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19486  ->
                        match uu____19486 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19516
                                 -> (p1, b)
                             | uu____19526 ->
                                 let uu____19527 =
                                   let uu____19530 =
                                     let uu____19531 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____19531
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____19530
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____19527, b))) sub_pats
                    in
                 let uu___2501_19535 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2501_19535.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19580  ->
                         match uu____19580 with
                         | (x,uu____19590) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19598
                                  -> false
                              | uu____19606 -> true)))
                  in
               let uu____19608 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____19608 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19645 =
                          let uu____19647 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____19649 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____19651 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____19658 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19647 uu____19649 uu____19651 uu____19658
                           in
                        failwith uu____19645)
                     else ();
                     (let uu____19663 =
                        let uu____19672 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____19672 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard) ->
                            let g' =
                              let uu____19700 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____19700  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____19703 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____19703
                              then
                                let uu____19708 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____19710 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____19712 =
                                  let uu____19714 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____19722 =
                                           let uu____19724 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____19726 =
                                             let uu____19728 =
                                               let uu____19730 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____19730 ")"
                                                in
                                             Prims.op_Hat " : " uu____19728
                                              in
                                           Prims.op_Hat uu____19724
                                             uu____19726
                                            in
                                         Prims.op_Hat "(" uu____19722)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____19714
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19708 uu____19710 uu____19712
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1))
                         in
                      match uu____19663 with
                      | (simple_pat_e1,simple_bvs1,g1) ->
                          let uu____19762 =
                            let uu____19784 =
                              let uu____19806 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], uu____19806)  in
                            FStar_List.fold_left2
                              (fun uu____19867  ->
                                 fun uu____19868  ->
                                   fun x  ->
                                     match (uu____19867, uu____19868) with
                                     | ((env2,bvs,pats,subst1,g),(p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____20001 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____20001 with
                                          | (bvs_p,e_p,p2,g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let uu____20042 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20042))) uu____19784
                              sub_pats1 simple_bvs1
                             in
                          (match uu____19762 with
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
                                              let uu___2573_20254 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2573_20254.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____20259 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____20259
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____20303)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20340 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____20340
                                             | uu____20360 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20386 ->
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
                                     let uu___2594_20429 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2594_20429.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20441 -> failwith "Impossible"  in
                               let uu____20445 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, pat_e, uu____20445, g))))))
           in
        (let uu____20449 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____20449
         then
           let uu____20454 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20454
         else ());
        (let uu____20459 =
           let uu____20470 =
             let uu___2599_20471 =
               let uu____20472 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____20472 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2599_20471.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2599_20471.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2599_20471.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2599_20471.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2599_20471.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2599_20471.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2599_20471.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2599_20471.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2599_20471.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2599_20471.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2599_20471.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2599_20471.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2599_20471.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2599_20471.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2599_20471.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2599_20471.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2599_20471.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2599_20471.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2599_20471.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2599_20471.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2599_20471.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2599_20471.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2599_20471.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2599_20471.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2599_20471.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2599_20471.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2599_20471.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2599_20471.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2599_20471.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2599_20471.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2599_20471.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2599_20471.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2599_20471.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2599_20471.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2599_20471.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2599_20471.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2599_20471.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2599_20471.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2599_20471.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2599_20471.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2599_20471.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2599_20471.FStar_TypeChecker_Env.nbe)
             }  in
           let uu____20488 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____20470 uu____20488 pat_t  in
         match uu____20459 with
         | (bvs,pat_e,pat,g) ->
             ((let uu____20512 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____20512
               then
                 let uu____20517 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____20519 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20517
                   uu____20519
               else ());
              (let uu____20524 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____20525 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, uu____20524, pat_e, uu____20525, g))))

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
          (Prims.bool -> FStar_Syntax_Syntax.lcomp) *
          FStar_TypeChecker_Env.guard_t))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____20571 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____20571 with
        | (pattern,when_clause,branch_exp) ->
            let uu____20617 = branch1  in
            (match uu____20617 with
             | (cpat,uu____20659,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____20681 =
                   let uu____20688 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____20688
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____20681 with
                  | (scrutinee_env,uu____20722) ->
                      let uu____20727 = tc_pat env pat_t pattern  in
                      (match uu____20727 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp,guard_pat)
                           ->
                           let uu____20778 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____20808 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____20808
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____20831 =
                                      let uu____20838 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____20838 e  in
                                    match uu____20831 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____20778 with
                            | (when_clause1,g_when) ->
                                let uu____20892 = tc_term pat_env branch_exp
                                   in
                                (match uu____20892 with
                                 | (branch_exp1,c,g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____20948 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _20959  ->
                                                  FStar_Pervasives_Native.Some
                                                    _20959) uu____20948
                                          in
                                       let uu____20960 =
                                         let eqs =
                                           let uu____20982 =
                                             let uu____20984 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____20984
                                              in
                                           if uu____20982
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____21000 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____21015 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____21018 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____21021 ->
                                                  let uu____21022 =
                                                    let uu____21025 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____21025 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____21022)
                                            in
                                         let uu____21028 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch
                                            in
                                         match uu____21028 with
                                         | (c1,g_branch1) ->
                                             let uu____21055 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____21072 when
                                                   let uu____21085 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____21085
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
                                                   let uu____21116 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____21117 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____21116, uu____21117)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____21138 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21138
                                                      in
                                                   let uu____21139 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____21140 =
                                                     let uu____21141 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21141 g_when
                                                      in
                                                   (uu____21139, uu____21140)
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
                                                   let uu____21159 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____21159, g_when)
                                                in
                                             (match uu____21055 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21202 =
                                                        should_return1 &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____21202
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____21207 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  let uu____21208 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21207, uu____21208))
                                          in
                                       match uu____20960 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21259 =
                                               let uu____21261 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____21261
                                                in
                                             if uu____21259
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21315 =
                                                      let uu____21323 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21323
                                                       in
                                                    match uu____21315 with
                                                    | (is_induc,datacons) ->
                                                        if
                                                          (Prims.op_Negation
                                                             is_induc)
                                                            ||
                                                            ((FStar_List.length
                                                                datacons)
                                                               >
                                                               (Prims.parse_int "1"))
                                                        then
                                                          let discriminator =
                                                            FStar_Syntax_Util.mk_discriminator
                                                              f.FStar_Syntax_Syntax.v
                                                             in
                                                          let uu____21339 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator
                                                             in
                                                          (match uu____21339
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> []
                                                           | uu____21360 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let disc1 =
                                                                 let uu____21376
                                                                   =
                                                                   let uu____21381
                                                                    =
                                                                    let uu____21382
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____21382]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21381
                                                                    in
                                                                 uu____21376
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let uu____21407
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool
                                                                  in
                                                               [uu____21407])
                                                        else []
                                                     in
                                                  let fail1 uu____21415 =
                                                    let uu____21416 =
                                                      let uu____21418 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____21420 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____21422 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21418
                                                        uu____21420
                                                        uu____21422
                                                       in
                                                    failwith uu____21416  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____21437) ->
                                                        head_constructor t1
                                                    | uu____21442 -> fail1 ()
                                                     in
                                                  let force_scrutinee
                                                    uu____21448 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____21449 =
                                                          let uu____21451 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p
                                                             in
                                                          let uu____21453 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2
                                                             in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21451
                                                            uu____21453
                                                           in
                                                        failwith uu____21449
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t
                                                     in
                                                  let pat_exp2 =
                                                    let uu____21460 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____21460
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21465,FStar_Syntax_Syntax.Tm_name
                                                     uu____21466) -> []
                                                  | (uu____21467,FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     )) -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21470 =
                                                        let uu____21471 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        let uu____21472 =
                                                          force_scrutinee ()
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21471
                                                          uu____21472
                                                          pat_exp2
                                                         in
                                                      [uu____21470]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21473,FStar_Pervasives_Native.Some
                                                      uu____21474)),uu____21475)
                                                      ->
                                                      let uu____21492 =
                                                        let uu____21499 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env
                                                           in
                                                        match uu____21499
                                                        with
                                                        | (env1,uu____21513)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2
                                                         in
                                                      (match uu____21492 with
                                                       | (uu____21520,t,uu____21522)
                                                           ->
                                                           let uu____21523 =
                                                             let uu____21524
                                                               =
                                                               force_scrutinee
                                                                 ()
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21524
                                                               pat_exp2
                                                              in
                                                           [uu____21523])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21525,[]),FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21526) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21550 =
                                                        let uu____21552 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21552
                                                         in
                                                      if uu____21550
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21562 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21565 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21562
                                                           uu____21565)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21568,[]),FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21569) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21587 =
                                                        let uu____21589 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21589
                                                         in
                                                      if uu____21587
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21599 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21602 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21599
                                                           uu____21602)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21605,pat_args),FStar_Syntax_Syntax.Tm_app
                                                     (head1,args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____21652 =
                                                        (let uu____21656 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____21656)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args))
                                                         in
                                                      if uu____21652
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21684 =
                                                             let uu____21689
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____21689
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____21775
                                                                     ->
                                                                    match uu____21775
                                                                    with
                                                                    | 
                                                                    ((pi,uu____21797),
                                                                    (ei,uu____21799))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____21827
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____21827
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____21848
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____21860
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____21860
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____21862
                                                                    =
                                                                    let uu____21863
                                                                    =
                                                                    let uu____21868
                                                                    =
                                                                    let uu____21869
                                                                    =
                                                                    let uu____21878
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____21878
                                                                     in
                                                                    [uu____21869]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____21868
                                                                     in
                                                                    uu____21863
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____21862
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____21684
                                                             FStar_List.flatten
                                                            in
                                                         let uu____21901 =
                                                           let uu____21904 =
                                                             force_scrutinee
                                                               ()
                                                              in
                                                           discriminate
                                                             uu____21904 f
                                                            in
                                                         FStar_List.append
                                                           uu____21901
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____21907,uu____21908)
                                                      -> []
                                                  | uu____21915 ->
                                                      let uu____21920 =
                                                        let uu____21922 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2
                                                           in
                                                        let uu____21924 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2
                                                           in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____21922
                                                          uu____21924
                                                         in
                                                      failwith uu____21920
                                                   in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____21953 =
                                                    let uu____21955 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____21955
                                                     in
                                                  if uu____21953
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____21961 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____21961
                                                        in
                                                     let uu____21970 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____21970 with
                                                     | (k,uu____21976) ->
                                                         let uu____21977 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____21977
                                                          with
                                                          | (t1,uu____21985,uu____21986)
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
                                           ((let uu____21998 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____21998
                                             then
                                               let uu____22001 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____22001
                                             else ());
                                            (let uu____22007 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____22024 =
                                               let uu____22025 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____22025 guard
                                                in
                                             (uu____22007, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____22024))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____22072 = check_let_bound_def true env1 lb  in
          (match uu____22072 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____22098 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____22120 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____22120, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22126 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____22126
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____22127 =
                      let uu____22140 =
                        let uu____22155 =
                          let uu____22164 =
                            let uu____22171 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____22171)
                             in
                          [uu____22164]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____22155
                         in
                      FStar_List.hd uu____22140  in
                    match uu____22127 with
                    | (uu____22207,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta;
                               FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                               FStar_TypeChecker_Env.CompressUvars;
                               FStar_TypeChecker_Env.NoFullNorm;
                               FStar_TypeChecker_Env.Exclude
                                 FStar_TypeChecker_Env.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Env.abstract_guard_n gvs g12  in
                        let uu____22221 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____22221))
                  in
               (match uu____22098 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____22238 =
                      let uu____22247 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____22247
                      then
                        let uu____22258 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____22258 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22292 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____22292
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22293 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____22293, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____22308 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____22308
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____22314 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____22314
                            then e2
                            else
                              ((let uu____22322 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____22322
                                  FStar_TypeChecker_Err.top_level_effect);
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect)))
                                 FStar_Pervasives_Native.None
                                 e2.FStar_Syntax_Syntax.pos)
                             in
                          (e21, c)))
                       in
                    (match uu____22238 with
                     | (e21,c12) ->
                         ((let uu____22346 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____22346
                           then
                             let uu____22349 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22349
                           else ());
                          (let e12 =
                             let uu____22355 = FStar_Options.tcnorm ()  in
                             if uu____22355
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
                           (let uu____22361 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____22361
                            then
                              let uu____22364 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22364
                            else ());
                           (let cres =
                              FStar_TypeChecker_Env.null_wp_for_eff env1
                                (FStar_Syntax_Util.comp_effect_name c12)
                                FStar_Syntax_Syntax.U_zero
                                FStar_Syntax_Syntax.t_unit
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
                            let uu____22373 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____22387 =
                              FStar_Syntax_Util.lcomp_of_comp cres  in
                            (uu____22373, uu____22387,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22388 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____22399 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____22399
        then
          let universe_of_binders bs =
            let uu____22426 =
              FStar_List.fold_left
                (fun uu____22451  ->
                   fun b  ->
                     match uu____22451 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____22426 with | (uu____22499,us) -> FStar_List.rev us
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
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___2911_22535 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2911_22535.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2911_22535.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2911_22535.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2911_22535.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2911_22535.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2911_22535.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2911_22535.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2911_22535.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2911_22535.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2911_22535.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2911_22535.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2911_22535.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2911_22535.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2911_22535.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2911_22535.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2911_22535.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2911_22535.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2911_22535.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2911_22535.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2911_22535.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2911_22535.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2911_22535.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2911_22535.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2911_22535.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2911_22535.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2911_22535.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2911_22535.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2911_22535.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2911_22535.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2911_22535.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2911_22535.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2911_22535.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2911_22535.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2911_22535.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2911_22535.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2911_22535.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2911_22535.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2911_22535.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2911_22535.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2911_22535.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2911_22535.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2911_22535.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____22537 =
            let uu____22549 =
              let uu____22550 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____22550 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____22549 lb  in
          (match uu____22537 with
           | (e1,uu____22573,c1,g1,annotated) ->
               let pure_or_ghost =
                 FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs
                  in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____22587 =
                     let uu____22593 =
                       let uu____22595 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____22597 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____22595 uu____22597
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____22593)
                      in
                   FStar_Errors.raise_error uu____22587
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____22608 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_Syntax_Syntax.res_typ)
                      in
                   if uu____22608
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___2926_22620 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2926_22620.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2926_22620.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____22621 =
                   let uu____22626 =
                     let uu____22627 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____22627]  in
                   FStar_Syntax_Subst.open_term uu____22626 e2  in
                 match uu____22621 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____22671 = tc_term env_x e21  in
                     (match uu____22671 with
                      | (e22,c2,g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_Syntax_Syntax.res_typ c2
                             in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c21.FStar_Syntax_Syntax.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_Syntax_Syntax.res_typ
                              cres.FStar_Syntax_Syntax.eff_name e11 attrs
                              lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____22697 =
                              let uu____22704 =
                                let uu____22705 =
                                  let uu____22719 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____22719)  in
                                FStar_Syntax_Syntax.Tm_let uu____22705  in
                              FStar_Syntax_Syntax.mk uu____22704  in
                            uu____22697 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____22737 =
                              let uu____22738 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____22739 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____22738
                                c1.FStar_Syntax_Syntax.res_typ uu____22739
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _22740  ->
                                 FStar_TypeChecker_Common.NonTrivial _22740)
                              uu____22737
                             in
                          let g21 =
                            let uu____22742 =
                              let uu____22743 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____22743 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____22742
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____22746 =
                            let uu____22748 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____22748  in
                          if uu____22746
                          then
                            let tt =
                              let uu____22759 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____22759
                                FStar_Option.get
                               in
                            ((let uu____22765 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____22765
                              then
                                let uu____22770 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____22772 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____22770 uu____22772
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____22779 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____22779 with
                             | (t,g_ex) ->
                                 ((let uu____22793 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____22793
                                   then
                                     let uu____22798 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____22800 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____22798 uu____22800
                                   else ());
                                  (let uu____22805 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___2959_22807 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___2959_22807.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___2959_22807.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___2959_22807.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____22805))))))))
      | uu____22808 ->
          failwith "Impossible (inner let with more than one lb)"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____22844 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____22844 with
           | (lbs1,e21) ->
               let uu____22863 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____22863 with
                | (env0,topt) ->
                    let uu____22882 = build_let_rec_env true env0 lbs1  in
                    (match uu____22882 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____22905 = check_let_recs rec_env lbs2  in
                         (match uu____22905 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____22925 =
                                  let uu____22926 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____22926
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____22925
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____22932 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____22932
                                  (fun _22949  ->
                                     FStar_Pervasives_Native.Some _22949)
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
                                     let uu____22986 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____23020 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____23020)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____22986
                                      in
                                   FStar_List.map2
                                     (fun uu____23055  ->
                                        fun lb  ->
                                          match uu____23055 with
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
                                let uu____23103 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____23103
                                 in
                              let uu____23104 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____23104 with
                               | (lbs5,e22) ->
                                   ((let uu____23124 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____23124
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23125 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____23125, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23139 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____23175 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23175 with
           | (lbs1,e21) ->
               let uu____23194 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23194 with
                | (env0,topt) ->
                    let uu____23213 = build_let_rec_env false env0 lbs1  in
                    (match uu____23213 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23236 =
                           let uu____23243 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____23243
                             (fun uu____23266  ->
                                match uu____23266 with
                                | (lbs3,g) ->
                                    let uu____23285 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____23285))
                            in
                         (match uu____23236 with
                          | (lbs3,g_lbs) ->
                              let uu____23300 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3034_23323 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3034_23323.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3034_23323.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3037_23325 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3037_23325.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____23300 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____23352 = tc_term env2 e21  in
                                   (match uu____23352 with
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
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____23376 =
                                            let uu____23377 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23377 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23376
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres5 =
                                          let uu___3058_23387 = cres4  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___3058_23387.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___3058_23387.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___3058_23387.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____23395 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____23395))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____23396 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____23396 with
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
                                                  uu____23437 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____23438 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____23438 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3074_23452
                                                           = cres5  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___3074_23452.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___3074_23452.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___3074_23452.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____23453 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____23453))))))))))
      | uu____23454 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t))
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____23502 = FStar_Options.ml_ish ()  in
          if uu____23502
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____23510 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____23510 with
             | (formals,c) ->
                 let uu____23542 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____23542 with
                  | (actuals,uu____23553,uu____23554) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____23575 =
                          let uu____23581 =
                            let uu____23583 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____23585 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____23583 uu____23585
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____23581)
                           in
                        FStar_Errors.raise_error uu____23575
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____23593 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____23593 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____23624 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____23624)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____23643 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____23643)
                               in
                            let msg =
                              let uu____23648 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____23650 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____23648 uu____23650 formals_msg
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
        let uu____23662 =
          FStar_List.fold_left
            (fun uu____23695  ->
               fun lb  ->
                 match uu____23695 with
                 | (lbs1,env1,g_acc) ->
                     let uu____23720 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____23720 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____23743 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____23762 =
                                 let uu____23769 =
                                   let uu____23770 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____23770
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3120_23781 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3120_23781.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3120_23781.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3120_23781.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3120_23781.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3120_23781.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3120_23781.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3120_23781.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3120_23781.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3120_23781.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3120_23781.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3120_23781.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3120_23781.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3120_23781.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3120_23781.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3120_23781.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3120_23781.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3120_23781.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3120_23781.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3120_23781.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3120_23781.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3120_23781.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3120_23781.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3120_23781.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3120_23781.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3120_23781.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3120_23781.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3120_23781.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3120_23781.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3120_23781.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3120_23781.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3120_23781.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3120_23781.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3120_23781.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3120_23781.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3120_23781.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3120_23781.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3120_23781.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3120_23781.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3120_23781.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3120_23781.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3120_23781.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3120_23781.FStar_TypeChecker_Env.nbe)
                                    }) t uu____23769
                                  in
                               match uu____23762 with
                               | (t1,uu____23790,g) ->
                                   let uu____23792 =
                                     let uu____23793 =
                                       let uu____23794 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____23794
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____23793
                                      in
                                   let uu____23795 = norm env01 t1  in
                                   (uu____23792, uu____23795))
                             in
                          (match uu____23743 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____23815 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____23815
                                 then
                                   let uu___3130_23818 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3130_23818.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3130_23818.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3130_23818.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3130_23818.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3130_23818.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3130_23818.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3130_23818.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3130_23818.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3130_23818.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3130_23818.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3130_23818.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3130_23818.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3130_23818.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3130_23818.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3130_23818.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3130_23818.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3130_23818.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3130_23818.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3130_23818.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3130_23818.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3130_23818.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3130_23818.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3130_23818.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3130_23818.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3130_23818.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3130_23818.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3130_23818.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3130_23818.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3130_23818.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3130_23818.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3130_23818.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3130_23818.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3130_23818.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3130_23818.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3130_23818.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3130_23818.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3130_23818.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3130_23818.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3130_23818.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3130_23818.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3130_23818.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3130_23818.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3133_23832 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3133_23832.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3133_23832.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3133_23832.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3133_23832.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____23662 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____23858 =
        let uu____23867 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____23893 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____23893 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____23923 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____23923
                       | uu____23930 ->
                           let lb1 =
                             let uu___3150_23933 = lb  in
                             let uu____23934 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____23934;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3150_23933.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____23937 =
                             let uu____23944 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____23944
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____23937 with
                            | (e,c,g) ->
                                ((let uu____23953 =
                                    let uu____23955 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____23955  in
                                  if uu____23953
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
        FStar_All.pipe_right uu____23867 FStar_List.unzip  in
      match uu____23858 with
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
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t *
          Prims.bool))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____24011 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____24011 with
        | (env1,uu____24030) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____24038 = check_lbtyp top_level env lb  in
            (match uu____24038 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____24087 =
                     tc_maybe_toplevel_term
                       (let uu___3181_24096 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3181_24096.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3181_24096.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3181_24096.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3181_24096.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3181_24096.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3181_24096.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3181_24096.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3181_24096.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3181_24096.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3181_24096.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3181_24096.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3181_24096.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3181_24096.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3181_24096.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3181_24096.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3181_24096.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3181_24096.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3181_24096.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3181_24096.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3181_24096.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3181_24096.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3181_24096.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3181_24096.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3181_24096.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3181_24096.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3181_24096.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3181_24096.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3181_24096.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3181_24096.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3181_24096.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3181_24096.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3181_24096.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3181_24096.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3181_24096.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3181_24096.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3181_24096.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3181_24096.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3181_24096.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3181_24096.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3181_24096.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3181_24096.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3181_24096.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____24087 with
                   | (e12,c1,g1) ->
                       let uu____24111 =
                         let uu____24116 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24122  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____24116 e12 c1 wf_annot
                          in
                       (match uu____24111 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____24139 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____24139
                              then
                                let uu____24142 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____24144 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____24146 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24142 uu____24144 uu____24146
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____24185 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24185 with
             | (univ_opening,univ_vars1) ->
                 let uu____24218 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24218))
        | uu____24223 ->
            let uu____24224 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24224 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24274 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24274)
                 else
                   (let uu____24281 = FStar_Syntax_Util.type_u ()  in
                    match uu____24281 with
                    | (k,uu____24301) ->
                        let uu____24302 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____24302 with
                         | (t2,uu____24324,g) ->
                             ((let uu____24327 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____24327
                               then
                                 let uu____24330 =
                                   let uu____24332 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____24332
                                    in
                                 let uu____24333 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24330 uu____24333
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____24339 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24339))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____24345  ->
      match uu____24345 with
      | (x,imp) ->
          let uu____24372 = FStar_Syntax_Util.type_u ()  in
          (match uu____24372 with
           | (tu,u) ->
               ((let uu____24394 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____24394
                 then
                   let uu____24397 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____24399 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____24401 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____24397 uu____24399 uu____24401
                 else ());
                (let uu____24406 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____24406 with
                 | (t,uu____24428,g) ->
                     let uu____24430 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____24446 = tc_tactic env tau  in
                           (match uu____24446 with
                            | (tau1,uu____24460,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____24464 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____24430 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3243_24499 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3243_24499.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3243_24499.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____24501 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____24501
                            then
                              let uu____24504 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____24508 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____24504
                                uu____24508
                            else ());
                           (let uu____24513 = push_binding env x1  in
                            (x1, uu____24513, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____24525 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____24525
       then
         let uu____24528 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____24528
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____24641 = tc_binder env1 b  in
             (match uu____24641 with
              | (b1,env',g,u) ->
                  let uu____24690 = aux env' bs2  in
                  (match uu____24690 with
                   | (bs3,env'1,g',us) ->
                       let uu____24751 =
                         let uu____24752 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____24752  in
                       ((b1 :: bs3), env'1, uu____24751, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Env.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____24860  ->
             fun uu____24861  ->
               match (uu____24860, uu____24861) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____24953 = tc_term en1 t  in
                     match uu____24953 with
                     | (t1,uu____24973,g') ->
                         let uu____24975 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____24975)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____25029  ->
             match uu____25029 with
             | (pats1,g) ->
                 let uu____25056 = tc_args en p  in
                 (match uu____25056 with
                  | (args,g') ->
                      let uu____25069 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____25069))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____25082 = tc_maybe_toplevel_term env e  in
      match uu____25082 with
      | (e1,c,g) ->
          let uu____25098 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____25098
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____25112 =
               let uu____25118 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____25118
               then
                 let uu____25126 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____25126, false)
               else
                 (let uu____25131 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____25131, true))
                in
             match uu____25112 with
             | (target_comp,allow_ghost) ->
                 let uu____25144 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____25144 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____25154 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____25155 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____25154, uu____25155)
                  | uu____25156 ->
                      if allow_ghost
                      then
                        let uu____25166 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____25166
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____25180 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____25180
                           e1.FStar_Syntax_Syntax.pos)))

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____25204 = tc_tot_or_gtot_term env t  in
      match uu____25204 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____25237 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25237
       then
         let uu____25242 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____25242
       else ());
      (let env1 =
         let uu___3325_25248 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3325_25248.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3325_25248.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3325_25248.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3325_25248.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3325_25248.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3325_25248.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3325_25248.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3325_25248.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3325_25248.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3325_25248.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3325_25248.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3325_25248.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3325_25248.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3325_25248.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3325_25248.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3325_25248.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3325_25248.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3325_25248.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3325_25248.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3325_25248.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3325_25248.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3325_25248.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3325_25248.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3325_25248.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3325_25248.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3325_25248.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3325_25248.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3325_25248.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3325_25248.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3325_25248.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3325_25248.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3325_25248.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3325_25248.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3325_25248.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3325_25248.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3325_25248.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3325_25248.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3325_25248.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3325_25248.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3325_25248.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3325_25248.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____25256 =
         try
           (fun uu___3329_25270  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____25291) ->
             let uu____25294 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____25294
          in
       match uu____25256 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____25312 = FStar_Syntax_Util.is_total_lcomp c1  in
           if uu____25312
           then (t, (c1.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____25323 =
                let uu____25329 =
                  let uu____25331 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25331
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25329)
                 in
              let uu____25335 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____25323 uu____25335))
  
let level_of_type_fail :
  'Auu____25351 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25351
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____25369 =
          let uu____25375 =
            let uu____25377 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____25377 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25375)  in
        let uu____25381 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____25369 uu____25381
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____25415 =
            let uu____25416 = FStar_Syntax_Util.unrefine t1  in
            uu____25416.FStar_Syntax_Syntax.n  in
          match uu____25415 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____25420 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____25426 = FStar_Syntax_Util.type_u ()  in
                 match uu____25426 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3361_25434 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3361_25434.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3361_25434.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3361_25434.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3361_25434.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3361_25434.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3361_25434.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3361_25434.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3361_25434.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3361_25434.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3361_25434.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3361_25434.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3361_25434.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3361_25434.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3361_25434.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3361_25434.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3361_25434.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3361_25434.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3361_25434.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3361_25434.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3361_25434.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3361_25434.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3361_25434.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3361_25434.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3361_25434.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3361_25434.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3361_25434.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3361_25434.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3361_25434.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3361_25434.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3361_25434.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3361_25434.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3361_25434.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3361_25434.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3361_25434.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3361_25434.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3361_25434.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3361_25434.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3361_25434.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3361_25434.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3361_25434.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3361_25434.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3361_25434.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25439 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____25439
                       | uu____25441 ->
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
      let uu____25458 =
        let uu____25459 = FStar_Syntax_Subst.compress e  in
        uu____25459.FStar_Syntax_Syntax.n  in
      match uu____25458 with
      | FStar_Syntax_Syntax.Tm_bvar uu____25462 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____25465 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____25489 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____25506) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____25551) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____25558 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25558 with | ((uu____25567,t),uu____25569) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____25575 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____25575
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25578,(FStar_Util.Inl t,uu____25580),uu____25581) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25628,(FStar_Util.Inr c,uu____25630),uu____25631) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____25679 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____25688;
             FStar_Syntax_Syntax.vars = uu____25689;_},us)
          ->
          let uu____25695 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25695 with
           | ((us',t),uu____25706) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____25713 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____25713)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____25732 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____25734 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____25743) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____25770 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____25770 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____25790  ->
                      match uu____25790 with
                      | (b,uu____25798) ->
                          let uu____25803 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____25803) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____25808 = universe_of_aux env res  in
                 level_of_type env res uu____25808  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____25919 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____25935 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____25973 ->
                let uu____25974 = universe_of_aux env hd3  in
                (uu____25974, args1)
            | FStar_Syntax_Syntax.Tm_name uu____25985 ->
                let uu____25986 = universe_of_aux env hd3  in
                (uu____25986, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____25997 ->
                let uu____26010 = universe_of_aux env hd3  in
                (uu____26010, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____26021 ->
                let uu____26028 = universe_of_aux env hd3  in
                (uu____26028, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____26039 ->
                let uu____26066 = universe_of_aux env hd3  in
                (uu____26066, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____26077 ->
                let uu____26084 = universe_of_aux env hd3  in
                (uu____26084, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____26095 ->
                let uu____26096 = universe_of_aux env hd3  in
                (uu____26096, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____26107 ->
                let uu____26122 = universe_of_aux env hd3  in
                (uu____26122, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26133 ->
                let uu____26140 = universe_of_aux env hd3  in
                (uu____26140, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26151 ->
                let uu____26152 = universe_of_aux env hd3  in
                (uu____26152, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26163,hd4::uu____26165) ->
                let uu____26230 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____26230 with
                 | (uu____26245,uu____26246,hd5) ->
                     let uu____26264 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____26264 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____26321 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____26323 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____26323 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____26381 ->
                let uu____26382 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____26382 with
                 | (env1,uu____26404) ->
                     let env2 =
                       let uu___3522_26410 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3522_26410.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3522_26410.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3522_26410.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3522_26410.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3522_26410.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3522_26410.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3522_26410.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3522_26410.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3522_26410.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3522_26410.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3522_26410.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3522_26410.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3522_26410.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3522_26410.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3522_26410.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3522_26410.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3522_26410.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3522_26410.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3522_26410.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3522_26410.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3522_26410.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3522_26410.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3522_26410.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3522_26410.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3522_26410.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3522_26410.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3522_26410.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3522_26410.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3522_26410.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3522_26410.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3522_26410.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3522_26410.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3522_26410.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3522_26410.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3522_26410.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3522_26410.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3522_26410.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3522_26410.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3522_26410.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3522_26410.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____26415 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____26415
                       then
                         let uu____26420 =
                           let uu____26422 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____26422  in
                         let uu____26423 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____26420 uu____26423
                       else ());
                      (let uu____26428 = tc_term env2 hd3  in
                       match uu____26428 with
                       | (uu____26449,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____26450;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____26452;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____26453;_},g)
                           ->
                           ((let uu____26467 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____26467 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____26478 = type_of_head true hd1 args  in
          (match uu____26478 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____26517 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____26517 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____26569 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____26569)))
      | FStar_Syntax_Syntax.Tm_match (uu____26571,hd1::uu____26573) ->
          let uu____26638 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____26638 with
           | (uu____26639,uu____26640,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____26658,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____26705 = universe_of_aux env e  in
      level_of_type env e uu____26705
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____26729 = tc_binders env tps  in
      match uu____26729 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____26787 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____26813 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26819 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____26819
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26821 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26821
            (fun uu____26835  ->
               match uu____26835 with
               | (t2,uu____26843) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26845;
             FStar_Syntax_Syntax.vars = uu____26846;_},us)
          ->
          let uu____26852 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26852
            (fun uu____26866  ->
               match uu____26866 with
               | (t2,uu____26874) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____26875) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____26877 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____26877
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____26879 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____26879
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____26884;_})
          ->
          let mk_comp =
            let uu____26928 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____26928
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____26959 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____26959
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____27029 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____27029
                 (fun u  ->
                    let uu____27037 =
                      let uu____27040 =
                        let uu____27047 =
                          let uu____27048 =
                            let uu____27063 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____27063)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____27048  in
                        FStar_Syntax_Syntax.mk uu____27047  in
                      uu____27040 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____27037))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27100 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27100 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27159 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____27159
                       (fun uc  ->
                          let uu____27167 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____27167)
                 | (x,imp)::bs3 ->
                     let uu____27193 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____27193
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27202 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27222) ->
          let uu____27227 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____27227
            (fun u_x  ->
               let uu____27235 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____27235)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27240;
             FStar_Syntax_Syntax.vars = uu____27241;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27320 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27320 with
           | (unary_op1,uu____27340) ->
               let head1 =
                 let uu____27368 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27368
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
             FStar_Syntax_Syntax.pos = uu____27416;
             FStar_Syntax_Syntax.vars = uu____27417;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27513 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27513 with
           | (unary_op1,uu____27533) ->
               let head1 =
                 let uu____27561 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____27561
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
             FStar_Syntax_Syntax.pos = uu____27617;
             FStar_Syntax_Syntax.vars = uu____27618;_},uu____27619::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____27658;
             FStar_Syntax_Syntax.vars = uu____27659;_},(t2,uu____27661)::uu____27662::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____27758 =
              let uu____27759 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____27759.FStar_Syntax_Syntax.n  in
            match uu____27758 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____27832 = FStar_Util.first_N n_args bs  in
                    match uu____27832 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____27920 =
                          let uu____27925 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____27925  in
                        (match uu____27920 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____27979 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____27979 with
                       | (bs1,c1) ->
                           let uu____28000 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____28000
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____28082  ->
                     match uu____28082 with
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
                         let uu____28158 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____28158)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____28160) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____28166,uu____28167) ->
                aux t2
            | uu____28208 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28209,(FStar_Util.Inl t2,uu____28211),uu____28212) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28259,(FStar_Util.Inr c,uu____28261),uu____28262) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____28327 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____28327
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____28335) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28340 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28363 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____28377 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____28388 = type_of_well_typed_term env t  in
      match uu____28388 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____28394;
            FStar_Syntax_Syntax.vars = uu____28395;_}
          -> FStar_Pervasives_Native.Some u
      | uu____28398 -> FStar_Pervasives_Native.None

let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3801_28426 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3801_28426.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3801_28426.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3801_28426.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3801_28426.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3801_28426.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3801_28426.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3801_28426.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3801_28426.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3801_28426.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3801_28426.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3801_28426.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3801_28426.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3801_28426.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3801_28426.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3801_28426.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3801_28426.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3801_28426.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3801_28426.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3801_28426.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3801_28426.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3801_28426.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3801_28426.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3801_28426.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3801_28426.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3801_28426.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3801_28426.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3801_28426.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3801_28426.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3801_28426.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3801_28426.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3801_28426.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3801_28426.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3801_28426.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3801_28426.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3801_28426.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3801_28426.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3801_28426.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3801_28426.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3801_28426.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3801_28426.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3801_28426.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3801_28426.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28433 =
            if must_total
            then
              let uu____28435 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28435 with | (uu____28442,uu____28443,g) -> g
            else
              (let uu____28447 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28447 with | (uu____28454,uu____28455,g) -> g)
             in
          let uu____28457 = type_of_well_typed_term env2 t  in
          match uu____28457 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____28462 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____28462
                then
                  let uu____28467 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____28469 = FStar_Syntax_Print.term_to_string t  in
                  let uu____28471 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____28473 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____28467 uu____28469 uu____28471 uu____28473
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____28482 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____28482
                 then
                   let uu____28487 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____28489 = FStar_Syntax_Print.term_to_string t  in
                   let uu____28491 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____28493 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____28487
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____28489 uu____28491 uu____28493
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None  -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
  
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3832_28530 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3832_28530.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3832_28530.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3832_28530.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3832_28530.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3832_28530.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3832_28530.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3832_28530.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3832_28530.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3832_28530.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3832_28530.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3832_28530.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3832_28530.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3832_28530.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3832_28530.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3832_28530.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3832_28530.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3832_28530.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3832_28530.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3832_28530.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3832_28530.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3832_28530.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3832_28530.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3832_28530.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3832_28530.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3832_28530.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3832_28530.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3832_28530.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3832_28530.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3832_28530.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3832_28530.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3832_28530.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3832_28530.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3832_28530.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3832_28530.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3832_28530.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3832_28530.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3832_28530.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3832_28530.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3832_28530.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3832_28530.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3832_28530.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3832_28530.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28537 =
            if must_total
            then
              let uu____28539 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28539 with | (uu____28546,uu____28547,g) -> g
            else
              (let uu____28551 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28551 with | (uu____28558,uu____28559,g) -> g)
             in
          let uu____28561 =
            let uu____28563 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____28563  in
          if uu____28561
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  