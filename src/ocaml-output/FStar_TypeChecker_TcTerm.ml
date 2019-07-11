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
                             let uu____844 =
                               let uu____845 =
                                 FStar_All.pipe_right ct
                                   (env.FStar_TypeChecker_Env.universe_of env)
                                  in
                               FStar_TypeChecker_Env.null_wp_for_eff env
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 uu____845 ct
                                in
                             FStar_Pervasives_Native.Some uu____844  in
                           (uu____841, c, true))))
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
                        let uu____875 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____875
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____878 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low
                           in
                        if uu____878
                        then
                          let uu____882 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____884 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____886 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____882 uu____884 uu____886
                        else ());
                       (let uu____891 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____891 with
                        | (e1,uu____905,g) ->
                            let g1 =
                              let uu____908 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____908
                                "could not prove post-condition" g
                               in
                            ((let uu____911 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____911
                              then
                                let uu____914 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____916 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____914 uu____916
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
  'Auu____934 'Auu____935 .
    FStar_TypeChecker_Env.env ->
      ('Auu____934 * 'Auu____935 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____934 * 'Auu____935 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____957  ->
      match uu____957 with
      | (te,kt,f) ->
          let uu____967 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____967 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____975 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____981 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____975 uu____981)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____994 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____994 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____999 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____999
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1041 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1041 with
        | (head1,args) ->
            let uu____1086 =
              let uu____1101 =
                let uu____1102 = FStar_Syntax_Util.un_uinst head1  in
                uu____1102.FStar_Syntax_Syntax.n  in
              (uu____1101, args)  in
            (match uu____1086 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1118) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1145,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1146))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1223,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1224))::(pat,FStar_Pervasives_Native.None
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
             | uu____1308 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1339 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1339) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1375 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1382 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1375 uu____1382  in
          let uu____1383 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1410  ->
                    match uu____1410 with
                    | (b,uu____1417) ->
                        let uu____1418 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1418))
             in
          match uu____1383 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1425) ->
              let uu____1430 =
                let uu____1436 =
                  let uu____1438 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1438
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1436)  in
              FStar_Errors.log_issue rng uu____1430
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1464 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1464 with
        | (head1,args) ->
            let uu____1509 =
              let uu____1524 =
                let uu____1525 = FStar_Syntax_Util.un_uinst head1  in
                uu____1525.FStar_Syntax_Syntax.n  in
              (uu____1524, args)  in
            (match uu____1509 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1541) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1563::(hd1,uu____1565)::(tl1,uu____1567)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1634 = pat_terms hd1  in
                 let uu____1637 = pat_terms tl1  in
                 FStar_List.append uu____1634 uu____1637
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1641::(pat,uu____1643)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1728 -> [])
         in
      let rec aux t1 =
        let uu____1753 =
          let uu____1754 = FStar_Syntax_Subst.compress t1  in
          uu____1754.FStar_Syntax_Syntax.n  in
        match uu____1753 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1759 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1760 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1761 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1762 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1775 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1776 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1777 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1796 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1811 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1818 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1841 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1855 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1878 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1886 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____1886 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____1919 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____1936  ->
                   match uu____1936 with
                   | (t3,uu____1948) ->
                       let uu____1953 = aux t3  in
                       FStar_List.append acc uu____1953) uu____1919 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1957,uu____1958) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2000) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2006) -> aux t2  in
      let tlist =
        let uu____2014 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2014 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = (Prims.parse_int "0")
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2037 =
                    let uu____2039 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2039  in
                  Prims.op_Hat s uu____2037) "" tlist
            in
         let uu____2043 =
           let uu____2049 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2049)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2043)
  
let check_smt_pat :
  'Auu____2064 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2064) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2105 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2105
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2108;
                  FStar_Syntax_Syntax.effect_name = uu____2109;
                  FStar_Syntax_Syntax.result_typ = uu____2110;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2114)::[];
                  FStar_Syntax_Syntax.flags = uu____2115;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2177 -> failwith "Impossible"
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
              let uu___349_2240 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___349_2240.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___349_2240.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___349_2240.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___349_2240.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___349_2240.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___349_2240.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___349_2240.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___349_2240.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___349_2240.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___349_2240.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___349_2240.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___349_2240.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___349_2240.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___349_2240.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___349_2240.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___349_2240.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___349_2240.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___349_2240.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___349_2240.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___349_2240.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___349_2240.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___349_2240.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___349_2240.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___349_2240.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___349_2240.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___349_2240.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___349_2240.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___349_2240.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___349_2240.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___349_2240.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___349_2240.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___349_2240.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___349_2240.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___349_2240.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___349_2240.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___349_2240.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.postprocess =
                  (uu___349_2240.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___349_2240.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___349_2240.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___349_2240.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___349_2240.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___349_2240.FStar_TypeChecker_Env.nbe)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2266 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2266
               then
                 let uu____2269 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2272 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2269 uu____2272
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2306  ->
                         match uu____2306 with
                         | (b,uu____2316) ->
                             let t =
                               let uu____2322 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2322
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2325 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2326 -> []
                              | uu____2341 ->
                                  let uu____2342 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2342])))
                  in
               let as_lex_list dec =
                 let uu____2355 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2355 with
                 | (head1,uu____2375) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2403 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2411 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2420  ->
                         match uu___1_2420 with
                         | FStar_Syntax_Syntax.DECREASES uu____2422 -> true
                         | uu____2426 -> false))
                  in
               match uu____2411 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2433 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2454 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2483 =
              match uu____2483 with
              | (l,t,u_names) ->
                  let uu____2507 =
                    let uu____2508 = FStar_Syntax_Subst.compress t  in
                    uu____2508.FStar_Syntax_Syntax.n  in
                  (match uu____2507 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2567  ->
                                 match uu____2567 with
                                 | (x,imp) ->
                                     let uu____2586 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2586
                                     then
                                       let uu____2595 =
                                         let uu____2596 =
                                           let uu____2599 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2599
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2596
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2595, imp)
                                     else (x, imp)))
                          in
                       let uu____2606 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2606 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2627 =
                                let uu____2632 =
                                  let uu____2633 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2642 =
                                    let uu____2653 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2653]  in
                                  uu____2633 :: uu____2642  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2632
                                 in
                              uu____2627 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2688 = FStar_Util.prefix formals2  in
                            (match uu____2688 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___416_2751 = last1  in
                                   let uu____2752 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___416_2751.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___416_2751.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2752
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2788 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____2788
                                   then
                                     let uu____2791 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2793 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2795 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2791 uu____2793 uu____2795
                                   else ());
                                  (l, t', u_names))))
                   | uu____2802 ->
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
               let uu____2866 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2866)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3479 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3479
       then
         let uu____3482 =
           let uu____3484 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3484  in
         let uu____3486 = FStar_Syntax_Print.term_to_string e  in
         let uu____3488 =
           let uu____3490 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3490  in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3482
           uu____3486 uu____3488
       else ());
      (let uu____3494 =
         FStar_Util.record_time
           (fun uu____3513  ->
              tc_maybe_toplevel_term
                (let uu___435_3516 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___435_3516.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___435_3516.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___435_3516.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___435_3516.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___435_3516.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___435_3516.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___435_3516.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___435_3516.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___435_3516.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___435_3516.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___435_3516.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___435_3516.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___435_3516.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___435_3516.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___435_3516.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___435_3516.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___435_3516.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___435_3516.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___435_3516.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___435_3516.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___435_3516.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___435_3516.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___435_3516.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___435_3516.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___435_3516.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___435_3516.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___435_3516.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___435_3516.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___435_3516.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___435_3516.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___435_3516.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___435_3516.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___435_3516.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___435_3516.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___435_3516.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___435_3516.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___435_3516.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___435_3516.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___435_3516.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___435_3516.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___435_3516.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___435_3516.FStar_TypeChecker_Env.nbe)
                 }) e)
          in
       match uu____3494 with
       | (r,ms) ->
           ((let uu____3541 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3541
             then
               ((let uu____3545 =
                   let uu____3547 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3547
                    in
                 let uu____3549 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3551 =
                   let uu____3553 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3553  in
                 let uu____3554 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3545 uu____3549 uu____3551 uu____3554);
                (let uu____3557 = r  in
                 match uu____3557 with
                 | (e1,uu____3565,uu____3566) ->
                     let uu____3567 =
                       let uu____3569 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3569
                        in
                     let uu____3571 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3573 =
                       let uu____3575 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3575  in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3567
                       uu____3571 uu____3573))
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
      (let uu____3593 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3593
       then
         let uu____3596 =
           let uu____3598 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3598  in
         let uu____3600 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3602 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3596 uu____3600
           uu____3602
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3613 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3643 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3650 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3663 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3664 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3665 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3666 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3667 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3686 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3701 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3708 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3724 =
             match uu___2_3724 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3730 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3746 =
                 let uu____3747 = FStar_Syntax_Subst.compress t  in
                 uu____3747.FStar_Syntax_Syntax.n  in
               match uu____3746 with
               | FStar_Syntax_Syntax.Tm_name uu____3751 -> true
               | uu____3753 -> false  in
             FStar_Util.for_some
               (fun uu____3763  ->
                  match uu____3763 with
                  | (uu____3769,t) ->
                      let uu____3771 = is_name1 t  in
                      Prims.op_Negation uu____3771)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3790  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3833  ->
                       match uu____3833 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___508_3862 = qi  in
                  let uu____3863 =
                    FStar_List.map
                      (fun uu____3891  ->
                         match uu____3891 with
                         | ((bv,uu____3907),bv') ->
                             let uu____3919 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____3919)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___508_3862.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3863
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
                         let uu____3931 =
                           let uu____3938 =
                             let uu____3939 =
                               let uu____3953 =
                                 let uu____3956 =
                                   let uu____3957 =
                                     let uu____3964 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____3964
                                      in
                                   [uu____3957]  in
                                 FStar_Syntax_Subst.close uu____3956 t  in
                               ((false, [lb]), uu____3953)  in
                             FStar_Syntax_Syntax.Tm_let uu____3939  in
                           FStar_Syntax_Syntax.mk uu____3938  in
                         uu____3931 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4000 =
                  FStar_List.fold_right
                    (fun uu____4036  ->
                       fun uu____4037  ->
                         match (uu____4036, uu____4037) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4106 = tc_term env_tm tm  in
                             (match uu____4106 with
                              | (tm1,uu____4124,g) ->
                                  let uu____4126 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4126))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4000 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___536_4168 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___536_4168.FStar_Syntax_Syntax.qkind);
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
                let uu____4187 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4187 with
                 | (env',uu____4201) ->
                     let uu____4206 =
                       tc_term
                         (let uu___545_4215 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___545_4215.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___545_4215.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___545_4215.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___545_4215.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___545_4215.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___545_4215.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___545_4215.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___545_4215.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___545_4215.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___545_4215.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___545_4215.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___545_4215.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___545_4215.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___545_4215.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___545_4215.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___545_4215.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___545_4215.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___545_4215.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___545_4215.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___545_4215.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___545_4215.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___545_4215.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___545_4215.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___545_4215.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___545_4215.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___545_4215.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___545_4215.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___545_4215.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___545_4215.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___545_4215.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___545_4215.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___545_4215.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___545_4215.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___545_4215.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___545_4215.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___545_4215.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___545_4215.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___545_4215.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___545_4215.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___545_4215.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___545_4215.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___545_4215.FStar_TypeChecker_Env.nbe)
                          }) qt
                        in
                     (match uu____4206 with
                      | (qt1,uu____4224,uu____4225) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4231 =
                            let uu____4238 =
                              let uu____4243 =
                                FStar_Syntax_Util.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4243  in
                            value_check_expected_typ env1 top uu____4238
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4231 with
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
           { FStar_Syntax_Syntax.blob = uu____4260;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4261;
             FStar_Syntax_Syntax.ltyp = uu____4262;
             FStar_Syntax_Syntax.rng = uu____4263;_}
           ->
           let uu____4274 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4274
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4281 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4281 with
            | (e2,c,g) ->
                let g1 =
                  let uu___575_4298 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___575_4298.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___575_4298.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___575_4298.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____4299 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4299, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4341 = FStar_Syntax_Util.type_u ()  in
           (match uu____4341 with
            | (t,u) ->
                let uu____4354 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4354 with
                 | (e2,c,g) ->
                     let uu____4370 =
                       let uu____4387 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4387 with
                       | (env2,uu____4411) -> tc_smt_pats env2 pats  in
                     (match uu____4370 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___598_4449 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___598_4449.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___598_4449.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___598_4449.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____4450 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4469 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4450, c, uu____4469))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4475 =
             let uu____4476 = FStar_Syntax_Subst.compress e1  in
             uu____4476.FStar_Syntax_Syntax.n  in
           (match uu____4475 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4485,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4487;
                               FStar_Syntax_Syntax.lbtyp = uu____4488;
                               FStar_Syntax_Syntax.lbeff = uu____4489;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4491;
                               FStar_Syntax_Syntax.lbpos = uu____4492;_}::[]),e2)
                ->
                let uu____4523 =
                  let uu____4530 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4530 e11  in
                (match uu____4523 with
                 | (e12,c1,g1) ->
                     let uu____4540 = tc_term env1 e2  in
                     (match uu____4540 with
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
                            let uu____4564 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_Syntax_Syntax.eff_name
                               in
                            if uu____4564
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4574 =
                              let uu____4581 =
                                let uu____4582 =
                                  let uu____4596 =
                                    let uu____4604 =
                                      let uu____4607 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4607]  in
                                    (false, uu____4604)  in
                                  (uu____4596, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4582  in
                              FStar_Syntax_Syntax.mk uu____4581  in
                            uu____4574 FStar_Pervasives_Native.None
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
                          let uu____4631 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4631)))
            | uu____4632 ->
                let uu____4633 = tc_term env1 e1  in
                (match uu____4633 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4655) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4667) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4686 = tc_term env1 e1  in
           (match uu____4686 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4710) ->
           let uu____4757 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4757 with
            | (env0,uu____4771) ->
                let uu____4776 = tc_comp env0 expected_c  in
                (match uu____4776 with
                 | (expected_c1,uu____4790,g) ->
                     let uu____4792 =
                       let uu____4799 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4799 e1  in
                     (match uu____4792 with
                      | (e2,c',g') ->
                          let uu____4809 =
                            let uu____4816 =
                              let uu____4821 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____4821)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____4816
                             in
                          (match uu____4809 with
                           | (e3,expected_c2,g'') ->
                               let uu____4831 = tc_tactic_opt env0 topt  in
                               (match uu____4831 with
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
                                      let uu____4891 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____4891
                                       in
                                    let uu____4892 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____4892 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____4909 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____4909
                                            in
                                         let uu____4910 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____4910)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____4914) ->
           let uu____4961 = FStar_Syntax_Util.type_u ()  in
           (match uu____4961 with
            | (k,u) ->
                let uu____4974 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____4974 with
                 | (t1,uu____4988,f) ->
                     let uu____4990 = tc_tactic_opt env1 topt  in
                     (match uu____4990 with
                      | (topt1,gtac) ->
                          let uu____5009 =
                            let uu____5016 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5016 e1  in
                          (match uu____5009 with
                           | (e2,c,g) ->
                               let uu____5026 =
                                 let uu____5031 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5037  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5031 e2 c f
                                  in
                               (match uu____5026 with
                                | (c1,f1) ->
                                    let uu____5047 =
                                      let uu____5054 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5054
                                        c1
                                       in
                                    (match uu____5047 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5101 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5101
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5103 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5103)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5104;
              FStar_Syntax_Syntax.vars = uu____5105;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5184 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5184 with
            | (unary_op1,uu____5208) ->
                let head1 =
                  let uu____5236 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5236
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
              FStar_Syntax_Syntax.pos = uu____5284;
              FStar_Syntax_Syntax.vars = uu____5285;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5364 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5364 with
            | (unary_op1,uu____5388) ->
                let head1 =
                  let uu____5416 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5416
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
                (FStar_Const.Const_reflect uu____5464);
              FStar_Syntax_Syntax.pos = uu____5465;
              FStar_Syntax_Syntax.vars = uu____5466;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5545 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5545 with
            | (unary_op1,uu____5569) ->
                let head1 =
                  let uu____5597 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5597
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
              FStar_Syntax_Syntax.pos = uu____5645;
              FStar_Syntax_Syntax.vars = uu____5646;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5742 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5742 with
            | (unary_op1,uu____5766) ->
                let head1 =
                  let uu____5794 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5794
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
              FStar_Syntax_Syntax.pos = uu____5850;
              FStar_Syntax_Syntax.vars = uu____5851;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____5889 =
             let uu____5896 =
               let uu____5897 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5897  in
             tc_term uu____5896 e1  in
           (match uu____5889 with
            | (e2,c,g) ->
                let uu____5921 = FStar_Syntax_Util.head_and_args top  in
                (match uu____5921 with
                 | (head1,uu____5945) ->
                     let uu____5970 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6003 =
                       let uu____6004 =
                         let uu____6005 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6005  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____6004
                        in
                     (uu____5970, uu____6003, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6006;
              FStar_Syntax_Syntax.vars = uu____6007;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6060 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6060 with
            | (head1,uu____6084) ->
                let env' =
                  let uu____6110 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6110  in
                let uu____6111 = tc_term env' r  in
                (match uu____6111 with
                 | (er,uu____6125,gr) ->
                     let uu____6127 = tc_term env1 t  in
                     (match uu____6127 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6144 =
                            let uu____6145 =
                              let uu____6150 =
                                let uu____6151 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6160 =
                                  let uu____6171 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6171]  in
                                uu____6151 :: uu____6160  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6150
                               in
                            uu____6145 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6144, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6204;
              FStar_Syntax_Syntax.vars = uu____6205;_},uu____6206)
           ->
           let uu____6231 =
             let uu____6237 =
               let uu____6239 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6239  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6237)  in
           FStar_Errors.raise_error uu____6231 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6249;
              FStar_Syntax_Syntax.vars = uu____6250;_},uu____6251)
           ->
           let uu____6276 =
             let uu____6282 =
               let uu____6284 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6284  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6282)  in
           FStar_Errors.raise_error uu____6276 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6294;
              FStar_Syntax_Syntax.vars = uu____6295;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6342 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6342 with
             | (env0,uu____6356) ->
                 let uu____6361 = tc_term env0 e1  in
                 (match uu____6361 with
                  | (e2,c,g) ->
                      let uu____6377 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6377 with
                       | (reify_op,uu____6401) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_Syntax_Syntax.res_typ
                              in
                           let ef =
                             let uu____6428 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_Syntax_Util.comp_effect_name uu____6428
                              in
                           ((let uu____6432 =
                               let uu____6434 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef
                                  in
                               Prims.op_Negation uu____6434  in
                             if uu____6432
                             then
                               let uu____6437 =
                                 let uu____6443 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str
                                    in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____6443)
                                  in
                               FStar_Errors.raise_error uu____6437
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____6450 =
                                 FStar_Syntax_Syntax.lcomp_comp c  in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____6450 u_c
                                in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let c1 =
                               let uu____6487 =
                                 FStar_TypeChecker_Env.is_total_effect env1
                                   ef
                                  in
                               if uu____6487
                               then
                                 let uu____6490 =
                                   FStar_Syntax_Syntax.mk_Total repr  in
                                 FStar_All.pipe_right uu____6490
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
                                  let uu____6502 =
                                    FStar_Syntax_Syntax.mk_Comp ct  in
                                  FStar_All.pipe_right uu____6502
                                    FStar_Syntax_Util.lcomp_of_comp)
                                in
                             let uu____6503 =
                               comp_check_expected_typ env1 e3 c1  in
                             match uu____6503 with
                             | (e4,c2,g') ->
                                 let uu____6519 =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 (e4, c2, uu____6519)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6521;
              FStar_Syntax_Syntax.vars = uu____6522;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6570 =
               let uu____6572 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6572  in
             if uu____6570
             then
               let uu____6575 =
                 let uu____6581 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6581)  in
               FStar_Errors.raise_error uu____6575 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6587 = FStar_Syntax_Util.head_and_args top  in
             match uu____6587 with
             | (reflect_op,uu____6611) ->
                 let uu____6636 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6636 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6676 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6676 with
                       | (env_no_ex,topt) ->
                           let uu____6695 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____6715 =
                                 let uu____6722 =
                                   let uu____6723 =
                                     let uu____6740 =
                                       let uu____6751 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6760 =
                                         let uu____6771 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6771]  in
                                       uu____6751 :: uu____6760  in
                                     (repr, uu____6740)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6723  in
                                 FStar_Syntax_Syntax.mk uu____6722  in
                               uu____6715 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6816 =
                               let uu____6823 =
                                 let uu____6824 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6824
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6823 t  in
                             match uu____6816 with
                             | (t1,uu____6850,g) ->
                                 let uu____6852 =
                                   let uu____6853 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____6853.FStar_Syntax_Syntax.n  in
                                 (match uu____6852 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____6866,(res,uu____6868)::(wp,uu____6870)::[])
                                      -> (t1, res, wp, g)
                                  | uu____6927 -> failwith "Impossible")
                              in
                           (match uu____6695 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____6953 =
                                  let uu____6960 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____6960 with
                                  | (e2,c,g) ->
                                      ((let uu____6977 =
                                          let uu____6979 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____6979
                                           in
                                        if uu____6977
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7002 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7002 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7013 =
                                                let uu____7023 =
                                                  let uu____7031 =
                                                    let uu____7033 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7035 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7033 uu____7035
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7031,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7023]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7013);
                                             (let uu____7053 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7053)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7057 =
                                              let uu____7058 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7058
                                               in
                                            (e2, uu____7057)))
                                   in
                                (match uu____6953 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7074 =
                                         let uu____7075 =
                                           let uu____7076 =
                                             let uu____7077 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7077]  in
                                           let uu____7078 =
                                             let uu____7089 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7089]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7076;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7078;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7075
                                          in
                                       FStar_All.pipe_right uu____7074
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7149 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7149 with
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
                                          let uu____7172 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7172))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7211 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7211 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7261,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7262))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7315 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7315 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7390 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7600 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7390 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7719 =
               let uu____7720 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7720 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7719 instantiate_both  in
           ((let uu____7736 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7736
             then
               let uu____7739 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7741 = FStar_Syntax_Print.term_to_string top  in
               let uu____7743 =
                 let uu____7745 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7745
                   (fun uu___3_7752  ->
                      match uu___3_7752 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7739
                 uu____7741 uu____7743
             else ());
            (let uu____7761 = tc_term (no_inst env2) head1  in
             match uu____7761 with
             | (head2,chead,g_head) ->
                 let uu____7777 =
                   let uu____7784 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____7787 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____7787))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____7784
                   then
                     let uu____7796 =
                       let uu____7803 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____7803
                        in
                     match uu____7796 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____7817 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____7817)
                    in
                 (match uu____7777 with
                  | (e1,c,g) ->
                      let uu____7829 =
                        let uu____7836 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____7836
                        then
                          let uu____7845 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____7845 with
                          | (e2,res_typ,implicits) ->
                              let uu____7861 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____7861, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____7829 with
                       | (e2,c1,implicits) ->
                           ((let uu____7874 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____7874
                             then
                               let uu____7877 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____7877
                             else ());
                            (let uu____7882 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____7882 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____7901 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____7901
                                   then
                                     let uu____7904 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____7906 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____7904 uu____7906
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____7949 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____7949 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____7969 = tc_term env12 e1  in
                (match uu____7969 with
                 | (e11,c1,g1) ->
                     let uu____7985 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____7999 = FStar_Syntax_Util.type_u ()  in
                           (match uu____7999 with
                            | (k,uu____8011) ->
                                let uu____8012 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8012 with
                                 | (res_t,uu____8033,g) ->
                                     let uu____8047 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8048 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8047, res_t, uu____8048)))
                        in
                     (match uu____7985 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8059 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8059
                            then
                              let uu____8062 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8062
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
                            let uu____8189 =
                              let uu____8194 =
                                FStar_List.fold_right
                                  (fun uu____8276  ->
                                     fun uu____8277  ->
                                       match (uu____8276, uu____8277) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____8522 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8522)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____8194 with
                              | (cases,g) ->
                                  let uu____8627 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8627, g)
                               in
                            match uu____8189 with
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
                                           (fun uu____8769  ->
                                              match uu____8769 with
                                              | ((pat,wopt,br),uu____8814,eff_label,uu____8816,uu____8817,uu____8818)
                                                  ->
                                                  let uu____8855 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____8855)))
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
                                  let uu____8922 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____8922
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____8930 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____8930  in
                                     let lb =
                                       let uu____8934 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____8934 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____8940 =
                                         let uu____8947 =
                                           let uu____8948 =
                                             let uu____8962 =
                                               let uu____8965 =
                                                 let uu____8966 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____8966]  in
                                               FStar_Syntax_Subst.close
                                                 uu____8965 e_match
                                                in
                                             ((false, [lb]), uu____8962)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____8948
                                            in
                                         FStar_Syntax_Syntax.mk uu____8947
                                          in
                                       uu____8940
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____8999 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____8999
                                  then
                                    let uu____9002 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9004 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____9002 uu____9004
                                  else ());
                                 (let uu____9009 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____9009))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9010;
                FStar_Syntax_Syntax.lbunivs = uu____9011;
                FStar_Syntax_Syntax.lbtyp = uu____9012;
                FStar_Syntax_Syntax.lbeff = uu____9013;
                FStar_Syntax_Syntax.lbdef = uu____9014;
                FStar_Syntax_Syntax.lbattrs = uu____9015;
                FStar_Syntax_Syntax.lbpos = uu____9016;_}::[]),uu____9017)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9043),uu____9044) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9062;
                FStar_Syntax_Syntax.lbunivs = uu____9063;
                FStar_Syntax_Syntax.lbtyp = uu____9064;
                FStar_Syntax_Syntax.lbeff = uu____9065;
                FStar_Syntax_Syntax.lbdef = uu____9066;
                FStar_Syntax_Syntax.lbattrs = uu____9067;
                FStar_Syntax_Syntax.lbpos = uu____9068;_}::uu____9069),uu____9070)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9098),uu____9099) ->
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
          let uu____9133 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9172))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9213 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9133 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9246 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9246 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9250 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9250)
                 in
              let uu____9253 =
                let uu____9260 =
                  let uu____9261 =
                    let uu____9262 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9262
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9261  in
                tc_term uu____9260 typ  in
              (match uu____9253 with
               | (typ1,uu____9278,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9281 = tc_tactic env tau  in
                     match uu____9281 with
                     | (tau1,uu____9295,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1195_9300 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1195_9300.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1195_9300.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9302 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9302
                            then
                              let uu____9307 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9307
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9313 =
                              let uu____9314 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_Syntax_Util.lcomp_of_comp uu____9314
                               in
                            (t, uu____9313,
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
        let uu___1203_9318 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1203_9318.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1203_9318.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1203_9318.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1203_9318.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1203_9318.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1203_9318.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1203_9318.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1203_9318.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1203_9318.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1203_9318.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1203_9318.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1203_9318.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1203_9318.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1203_9318.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1203_9318.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1203_9318.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1203_9318.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1203_9318.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1203_9318.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1203_9318.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1203_9318.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1203_9318.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1203_9318.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1203_9318.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1203_9318.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1203_9318.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1203_9318.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1203_9318.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1203_9318.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1203_9318.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1203_9318.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1203_9318.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1203_9318.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1203_9318.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1203_9318.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1203_9318.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1203_9318.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1203_9318.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1203_9318.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1203_9318.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1203_9318.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1203_9318.FStar_TypeChecker_Env.nbe)
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
          let uu____9341 = tc_tactic env tactic  in
          (match uu____9341 with
           | (tactic1,uu____9355,g) ->
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
        let uu____9407 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9407 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9428 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9428
              then FStar_Util.Inl t
              else
                (let uu____9437 =
                   let uu____9438 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____9438
                    in
                 FStar_Util.Inr uu____9437)
               in
            let is_data_ctor uu___4_9447 =
              match uu___4_9447 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9452) -> true
              | uu____9460 -> false  in
            let uu____9464 =
              (is_data_ctor dc) &&
                (let uu____9467 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9467)
               in
            if uu____9464
            then
              let uu____9476 =
                let uu____9482 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9482)  in
              let uu____9486 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9476 uu____9486
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9504 =
            let uu____9506 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9506
             in
          failwith uu____9504
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9533 =
            let uu____9538 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9538  in
          value_check_expected_typ env1 e uu____9533
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9540 =
            let uu____9553 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9553 with
            | FStar_Pervasives_Native.None  ->
                let uu____9568 = FStar_Syntax_Util.type_u ()  in
                (match uu____9568 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9540 with
           | (t,uu____9606,g0) ->
               let uu____9620 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____9620 with
                | (e1,uu____9641,g1) ->
                    let uu____9655 =
                      let uu____9656 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9656
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____9657 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9655, uu____9657)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9659 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9669 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9669)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9659 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1268_9683 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1268_9683.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1268_9683.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9686 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9686 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9707 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9707
                       then FStar_Util.Inl t1
                       else
                         (let uu____9716 =
                            let uu____9717 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____9717
                             in
                          FStar_Util.Inr uu____9716)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9719;
             FStar_Syntax_Syntax.vars = uu____9720;_},uu____9721)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9726 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9726
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9736 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9736
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9746;
             FStar_Syntax_Syntax.vars = uu____9747;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____9756 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9756 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9780 =
                     let uu____9786 =
                       let uu____9788 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____9790 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____9792 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9788 uu____9790 uu____9792
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9786)
                      in
                   let uu____9796 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____9780 uu____9796)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9813 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9818 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9818 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9820 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9820 with
           | ((us,t),range) ->
               ((let uu____9843 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____9843
                 then
                   let uu____9848 =
                     let uu____9850 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____9850  in
                   let uu____9851 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____9853 = FStar_Range.string_of_range range  in
                   let uu____9855 = FStar_Range.string_of_use_range range  in
                   let uu____9857 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____9848 uu____9851 uu____9853 uu____9855 uu____9857
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9865 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9865 us  in
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
          let uu____9893 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9893 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____9907 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9907 with
                | (env2,uu____9921) ->
                    let uu____9926 = tc_binders env2 bs1  in
                    (match uu____9926 with
                     | (bs2,env3,g,us) ->
                         let uu____9945 = tc_comp env3 c1  in
                         (match uu____9945 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1348_9964 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1348_9964.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1348_9964.FStar_Syntax_Syntax.vars)
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
                                  let uu____9975 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____9975
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
          let uu____9991 =
            let uu____9996 =
              let uu____9997 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____9997]  in
            FStar_Syntax_Subst.open_term uu____9996 phi  in
          (match uu____9991 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10025 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10025 with
                | (env2,uu____10039) ->
                    let uu____10044 =
                      let uu____10059 = FStar_List.hd x1  in
                      tc_binder env2 uu____10059  in
                    (match uu____10044 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10095 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10095
                           then
                             let uu____10098 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10100 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10102 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10098 uu____10100 uu____10102
                           else ());
                          (let uu____10109 = FStar_Syntax_Util.type_u ()  in
                           match uu____10109 with
                           | (t_phi,uu____10121) ->
                               let uu____10122 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10122 with
                                | (phi2,uu____10136,f2) ->
                                    let e1 =
                                      let uu___1386_10141 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1386_10141.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1386_10141.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10150 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10150
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10178) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10205 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10205
            then
              let uu____10208 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1399_10212 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1399_10212.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1399_10212.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10208
            else ());
           (let uu____10228 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10228 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10241 ->
          let uu____10242 =
            let uu____10244 = FStar_Syntax_Print.term_to_string top  in
            let uu____10246 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10244
              uu____10246
             in
          failwith uu____10242

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10258 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10260,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10273,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____10291 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10297 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10299 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10300 ->
            let uu____10302 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10302 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10307 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10308 =
              let uu____10314 =
                let uu____10316 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10316
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10314)  in
            FStar_Errors.raise_error uu____10308 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10320 =
              let uu____10326 =
                let uu____10328 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10328
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10326)  in
            FStar_Errors.raise_error uu____10320 r
        | FStar_Const.Const_reify  ->
            let uu____10332 =
              let uu____10338 =
                let uu____10340 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10340
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10338)  in
            FStar_Errors.raise_error uu____10332 r
        | FStar_Const.Const_reflect uu____10344 ->
            let uu____10345 =
              let uu____10351 =
                let uu____10353 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10353
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10351)  in
            FStar_Errors.raise_error uu____10345 r
        | uu____10357 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____10376) ->
          let uu____10385 = FStar_Syntax_Util.type_u ()  in
          (match uu____10385 with
           | (k,u) ->
               let uu____10398 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10398 with
                | (t1,uu____10412,g) ->
                    let uu____10414 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10414, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10416) ->
          let uu____10425 = FStar_Syntax_Util.type_u ()  in
          (match uu____10425 with
           | (k,u) ->
               let uu____10438 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10438 with
                | (t1,uu____10452,g) ->
                    let uu____10454 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10454, u, g)))
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
            let uu____10464 =
              let uu____10469 =
                let uu____10470 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10470 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10469  in
            uu____10464 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10487 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10487 with
           | (tc1,uu____10501,f) ->
               let uu____10503 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10503 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10553 =
                        let uu____10554 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10554.FStar_Syntax_Syntax.n  in
                      match uu____10553 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10557,us) -> us
                      | uu____10563 -> []  in
                    let uu____10564 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10564 with
                     | (uu____10587,args1) ->
                         let uu____10613 =
                           let uu____10636 = FStar_List.hd args1  in
                           let uu____10653 = FStar_List.tl args1  in
                           (uu____10636, uu____10653)  in
                         (match uu____10613 with
                          | (res,args2) ->
                              let uu____10734 =
                                let uu____10743 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10771  ->
                                          match uu___5_10771 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10779 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____10779 with
                                               | (env1,uu____10791) ->
                                                   let uu____10796 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____10796 with
                                                    | (e1,uu____10808,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____10743
                                  FStar_List.unzip
                                 in
                              (match uu____10734 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1528_10849 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1528_10849.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1528_10849.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____10855 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____10855))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____10865 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____10869 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____10879 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____10879
        | FStar_Syntax_Syntax.U_max us ->
            let uu____10883 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____10883
        | FStar_Syntax_Syntax.U_name x ->
            let uu____10887 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____10887
            then u2
            else
              (let uu____10892 =
                 let uu____10894 =
                   let uu____10896 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____10896 " not found"  in
                 Prims.op_Hat "Universe variable " uu____10894  in
               failwith uu____10892)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____10903 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____10903 FStar_Pervasives_Native.snd
         | uu____10912 -> aux u)

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
            let uu____10943 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____10943 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11032 bs2 bs_expected1 =
              match uu____11032 with
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
                              uu____11223),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11224)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11239),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11240)) -> true
                           | uu____11249 -> false  in
                         let uu____11259 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11262 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11262 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11259
                         then
                           let uu____11264 =
                             let uu____11270 =
                               let uu____11272 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11272
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11270)
                              in
                           let uu____11276 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11264 uu____11276
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11280 =
                           let uu____11287 =
                             let uu____11288 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11288.FStar_Syntax_Syntax.n  in
                           match uu____11287 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11299 ->
                               ((let uu____11301 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11301
                                 then
                                   let uu____11304 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11304
                                 else ());
                                (let uu____11309 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11309 with
                                 | (t,uu____11323,g1_env) ->
                                     let g2_env =
                                       let uu____11326 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11326
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11331 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11331 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11334 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11340 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11334 uu____11340
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____11342 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____11342
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11344 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11344)))
                            in
                         match uu____11280 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1626_11370 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1626_11370.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1626_11370.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11393 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11393
                                in
                             let uu____11396 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11396 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11461 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11461,
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
                  | uu____11633 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11643 = tc_binders env1 bs  in
                  match uu____11643 with
                  | (bs1,envbody,g_env,uu____11673) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____11729 =
                    let uu____11730 = FStar_Syntax_Subst.compress t2  in
                    uu____11730.FStar_Syntax_Syntax.n  in
                  match uu____11729 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11763 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11783 -> failwith "Impossible");
                       (let uu____11793 = tc_binders env1 bs  in
                        match uu____11793 with
                        | (bs1,envbody,g_env,uu____11835) ->
                            let uu____11836 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____11836 with
                             | (envbody1,uu____11874) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____11895;
                         FStar_Syntax_Syntax.pos = uu____11896;
                         FStar_Syntax_Syntax.vars = uu____11897;_},uu____11898)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11942 -> failwith "Impossible");
                       (let uu____11952 = tc_binders env1 bs  in
                        match uu____11952 with
                        | (bs1,envbody,g_env,uu____11994) ->
                            let uu____11995 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____11995 with
                             | (envbody1,uu____12033) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12055) ->
                      let uu____12060 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12060 with
                       | (uu____12121,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12198 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12198 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12343 c_expected2
                               body3 =
                               match uu____12343 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12457 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12457,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12474 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12474
                                           in
                                        let uu____12475 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12475,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12492 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12492
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
                                               let uu____12558 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12558 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12585 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12585 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12640 =
                                                           let uu____12667 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12667,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12640
                                                           c_expected4 body3))
                                           | uu____12690 ->
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
                             let uu____12719 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____12719 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1752_12784 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1752_12784.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1752_12784.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1752_12784.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1752_12784.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1752_12784.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1752_12784.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1752_12784.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1752_12784.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1752_12784.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1752_12784.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1752_12784.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1752_12784.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1752_12784.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1752_12784.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1752_12784.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1752_12784.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1752_12784.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1752_12784.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1752_12784.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1752_12784.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1752_12784.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1752_12784.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1752_12784.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1752_12784.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1752_12784.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1752_12784.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1752_12784.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1752_12784.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1752_12784.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1752_12784.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1752_12784.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1752_12784.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1752_12784.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1752_12784.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1752_12784.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1752_12784.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1752_12784.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1752_12784.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1752_12784.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1752_12784.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1752_12784.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1752_12784.FStar_TypeChecker_Env.nbe)
                               }  in
                             let uu____12791 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____12857  ->
                                       fun uu____12858  ->
                                         match (uu____12857, uu____12858)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____12949 =
                                               let uu____12956 =
                                                 let uu____12957 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____12957
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____12956 t3  in
                                             (match uu____12949 with
                                              | (t4,uu____12981,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____12994 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1770_12997
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1770_12997.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1770_12997.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____12994 ::
                                                          letrec_binders
                                                    | uu____12998 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13003 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13003)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____12791 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13023 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13023)
                              in
                           let uu____13026 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13026 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13102 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13102 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13149 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13149))))
                  | uu____13166 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13198 =
                          let uu____13199 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____13199
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____13198
                      else
                        (let uu____13203 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13203 with
                         | (uu____13252,bs1,uu____13254,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13286 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13286 with
          | (env1,topt) ->
              ((let uu____13306 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13306
                then
                  let uu____13309 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13309
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13323 = expected_function_typ1 env1 topt body  in
                match uu____13323 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13364 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____13364
                      then
                        let uu____13367 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        FStar_Util.print1
                          "Expected comp of the abstraction body: %s\n"
                          uu____13367
                      else ());
                     (let uu____13376 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13376
                      then
                        let uu____13381 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13384 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13381 uu____13384
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13390 =
                        let should_check_expected_effect =
                          let uu____13403 =
                            let uu____13410 =
                              let uu____13411 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13411.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13410)  in
                          match uu____13403 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13417,(FStar_Util.Inr
                                           expected_c,uu____13419),uu____13420))
                              -> false
                          | uu____13470 -> true  in
                        let uu____13478 =
                          tc_term
                            (let uu___1837_13487 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1837_13487.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1837_13487.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1837_13487.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1837_13487.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1837_13487.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1837_13487.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1837_13487.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1837_13487.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1837_13487.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1837_13487.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1837_13487.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1837_13487.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1837_13487.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1837_13487.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1837_13487.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1837_13487.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1837_13487.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1837_13487.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1837_13487.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1837_13487.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1837_13487.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1837_13487.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1837_13487.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1837_13487.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1837_13487.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1837_13487.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1837_13487.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1837_13487.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1837_13487.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1837_13487.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1837_13487.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1837_13487.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1837_13487.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1837_13487.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1837_13487.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1837_13487.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1837_13487.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1837_13487.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1837_13487.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1837_13487.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1837_13487.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____13478 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13514 =
                                let uu____13521 =
                                  let uu____13526 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____13526)  in
                                check_expected_effect
                                  (let uu___1845_13529 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___1845_13529.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___1845_13529.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___1845_13529.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___1845_13529.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___1845_13529.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___1845_13529.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___1845_13529.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___1845_13529.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___1845_13529.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___1845_13529.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___1845_13529.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___1845_13529.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___1845_13529.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___1845_13529.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___1845_13529.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___1845_13529.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___1845_13529.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___1845_13529.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___1845_13529.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___1845_13529.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___1845_13529.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___1845_13529.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___1845_13529.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___1845_13529.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___1845_13529.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___1845_13529.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___1845_13529.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___1845_13529.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___1845_13529.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___1845_13529.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___1845_13529.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___1845_13529.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___1845_13529.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___1845_13529.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___1845_13529.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___1845_13529.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___1845_13529.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___1845_13529.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___1845_13529.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___1845_13529.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___1845_13529.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___1845_13529.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____13521
                                 in
                              (match uu____13514 with
                               | (body3,cbody1,guard) ->
                                   let uu____13543 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____13543))
                            else
                              (let uu____13550 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____13550, guard_body1))
                         in
                      match uu____13390 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13575 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13578 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13578)
                               in
                            if uu____13575
                            then
                              let uu____13581 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13582 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13581
                                uu____13582
                            else
                              (let guard =
                                 let uu____13586 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13586
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
                          let uu____13600 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13621
                                     -> (e, t1, guard1)
                                 | uu____13636 ->
                                     let uu____13637 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13637 with
                                      | (e1,guard') ->
                                          let uu____13650 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____13650)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13600 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13661 =
                                 let uu____13666 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13666 guard2
                                  in
                               (match uu____13661 with
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
              (let uu____13715 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____13715
               then
                 let uu____13718 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____13720 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13718
                   uu____13720
               else ());
              (let monadic_application uu____13798 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____13798 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____13859 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____13859 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___1905_13873 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___1905_13873.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___1905_13873.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___1905_13873.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____13874 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____13890 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____13890
                                   in
                                (cres1, g)
                            | uu____13891 ->
                                let g =
                                  let uu____13901 =
                                    let uu____13902 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____13902
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____13901
                                   in
                                let uu____13903 =
                                  let uu____13904 =
                                    let uu____13905 =
                                      let uu____13906 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____13906
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____13905
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____13904
                                   in
                                (uu____13903, g)
                             in
                          (match uu____13874 with
                           | (cres2,guard1) ->
                               ((let uu____13918 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____13918
                                 then
                                   let uu____13921 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____13921
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____13941  ->
                                             match uu____13941 with
                                             | (uu____13951,uu____13952,lc)
                                                 ->
                                                 (let uu____13960 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____13960)
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
                                   let uu____13973 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____13973
                                   then
                                     ((let uu____13977 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13977
                                       then
                                         let uu____13980 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____13980
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____13988 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13988
                                       then
                                         let uu____13991 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____13991
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____14022  ->
                                          match uu____14022 with
                                          | ((e,q),x,c) ->
                                              ((let uu____14064 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14064
                                                then
                                                  let uu____14067 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____14072 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14074 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____14067 uu____14072
                                                    uu____14074
                                                else ());
                                               (let uu____14079 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14079
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
                                   (let uu____14090 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____14090
                                    then
                                      let uu____14093 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____14093
                                    else ());
                                   (let uu____14098 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____14098
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
                                   let uu____14110 =
                                     let uu____14111 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____14111.FStar_Syntax_Syntax.n  in
                                   match uu____14110 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____14116 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____14139  ->
                                              match uu____14139 with
                                              | (arg,uu____14153,uu____14154)
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
                                     (let uu____14165 =
                                        let map_fun uu____14231 =
                                          match uu____14231 with
                                          | ((e,q),uu____14272,c) ->
                                              ((let uu____14295 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14295
                                                then
                                                  let uu____14298 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14300 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____14298 uu____14300
                                                else ());
                                               (let uu____14305 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14305
                                                then
                                                  ((let uu____14331 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14331
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
                                                       (let uu____14372 =
                                                          let uu____14374 =
                                                            let uu____14375 =
                                                              FStar_Syntax_Util.un_uinst
                                                                head2
                                                               in
                                                            uu____14375.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____14374
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let uu____14380
                                                                =
                                                                FStar_Parser_Const.psconst
                                                                  "ignore"
                                                                 in
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv
                                                                uu____14380
                                                          | uu____14382 ->
                                                              true
                                                           in
                                                        Prims.op_Negation
                                                          uu____14372)
                                                      in
                                                   if warn_effectful_args
                                                   then
                                                     (let uu____14386 =
                                                        let uu____14392 =
                                                          let uu____14394 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e
                                                             in
                                                          let uu____14396 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head2
                                                             in
                                                          FStar_Util.format3
                                                            "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                            uu____14394
                                                            (c.FStar_Syntax_Syntax.eff_name).FStar_Ident.str
                                                            uu____14396
                                                           in
                                                        (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                          uu____14392)
                                                         in
                                                      FStar_Errors.log_issue
                                                        e.FStar_Syntax_Syntax.pos
                                                        uu____14386)
                                                   else ();
                                                   (let uu____14403 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14403
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
                                                    let uu____14411 =
                                                      let uu____14420 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____14420, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____14411)))))
                                           in
                                        let uu____14449 =
                                          let uu____14480 =
                                            let uu____14509 =
                                              let uu____14520 =
                                                let uu____14529 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____14529,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____14520 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____14509
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____14480
                                           in
                                        match uu____14449 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____14730 =
                                              let uu____14731 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____14731
                                               in
                                            let uu____14752 =
                                              let uu____14753 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____14753  in
                                            (lifted_args, uu____14730,
                                              uu____14752)
                                         in
                                      match uu____14165 with
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
                                          let bind_lifted_args e uu___6_14864
                                            =
                                            match uu___6_14864 with
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
                                                  let uu____14925 =
                                                    let uu____14932 =
                                                      let uu____14933 =
                                                        let uu____14947 =
                                                          let uu____14950 =
                                                            let uu____14951 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____14951]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____14950 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____14947)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____14933
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____14932
                                                     in
                                                  uu____14925
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
                                 let uu____15003 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____15003 with
                                 | (comp3,g) ->
                                     ((let uu____15021 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____15021
                                       then
                                         let uu____15024 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____15026 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____15024 uu____15026
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____15107 bs args1 =
                 match uu____15107 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15246))::rest,
                         (uu____15248,FStar_Pervasives_Native.None )::uu____15249)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15310 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15310 with
                           | (t1,g_ex) ->
                               let uu____15323 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15323 with
                                | (varg,uu____15344,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15372 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15372)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15381 =
                                      let uu____15416 =
                                        let uu____15427 =
                                          let uu____15436 =
                                            let uu____15437 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15437
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15436)
                                           in
                                        uu____15427 :: outargs  in
                                      (subst2, uu____15416, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15381 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15483,FStar_Pervasives_Native.None
                                                                 )::uu____15484)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15546 = tc_tactic env tau1  in
                          (match uu____15546 with
                           | (tau2,uu____15560,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15563 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15563 with
                                | (t1,g_ex) ->
                                    let uu____15576 =
                                      let uu____15589 =
                                        let uu____15596 =
                                          let uu____15601 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15601, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15596
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15589
                                       in
                                    (match uu____15576 with
                                     | (varg,uu____15614,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15642 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15642)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____15651 =
                                           let uu____15686 =
                                             let uu____15697 =
                                               let uu____15706 =
                                                 let uu____15707 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____15707
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15706)
                                                in
                                             uu____15697 :: outargs  in
                                           (subst2, uu____15686, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____15651 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____15823,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15824)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____15835),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15836)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____15844),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15845)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____15860 ->
                                let uu____15869 =
                                  let uu____15875 =
                                    let uu____15877 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____15879 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____15881 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____15883 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____15877 uu____15879 uu____15881
                                      uu____15883
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____15875)
                                   in
                                FStar_Errors.raise_error uu____15869
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2115_15890 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2115_15890.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2115_15890.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____15892 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____15892
                             then
                               let uu____15895 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____15897 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15899 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15901 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____15903 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____15895 uu____15897 uu____15899
                                 uu____15901 uu____15903
                             else ());
                            (let uu____15908 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____15908 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2124_15923 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2124_15923.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2124_15923.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2124_15923.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2124_15923.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2124_15923.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2124_15923.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2124_15923.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2124_15923.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2124_15923.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2124_15923.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2124_15923.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2124_15923.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2124_15923.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2124_15923.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2124_15923.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2124_15923.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2124_15923.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2124_15923.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2124_15923.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2124_15923.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2124_15923.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2124_15923.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2124_15923.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2124_15923.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2124_15923.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2124_15923.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2124_15923.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2124_15923.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2124_15923.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2124_15923.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2124_15923.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2124_15923.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2124_15923.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2124_15923.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2124_15923.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2124_15923.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2124_15923.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2124_15923.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2124_15923.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2124_15923.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2124_15923.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2124_15923.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____15925 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____15925
                                   then
                                     let uu____15928 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____15930 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____15932 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____15928 uu____15930 uu____15932
                                   else ());
                                  (let uu____15937 = tc_term env2 e  in
                                   match uu____15937 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____15954 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____15954
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____15977 =
                                           let uu____15980 =
                                             let uu____15989 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15989
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____15980
                                            in
                                         (uu____15977, aq)  in
                                       let uu____15998 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____15998
                                       then
                                         let subst2 =
                                           let uu____16008 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16008 e1
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
                      | (uu____16107,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16143) ->
                          let uu____16194 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16194 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____16250 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____16250
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____16281 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____16281 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____16303 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____16303)
                                             in
                                          ((let uu____16305 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____16305
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
                                 | uu____16352 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____16360 =
                                         let uu____16361 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____16361.FStar_Syntax_Syntax.n
                                          in
                                       match uu____16360 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____16364;
                                              FStar_Syntax_Syntax.index =
                                                uu____16365;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____16367)
                                           -> norm_tres tres4
                                       | uu____16375 -> tres3  in
                                     let uu____16376 = norm_tres tres1  in
                                     aux true solve ghead2 uu____16376
                                 | uu____16378 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____16381 ->
                                     let uu____16382 =
                                       let uu____16388 =
                                         let uu____16390 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____16392 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____16394 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____16390 uu____16392
                                           uu____16394
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____16388)
                                        in
                                     let uu____16398 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____16382
                                       uu____16398
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____16428 =
                   let uu____16429 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16429.FStar_Syntax_Syntax.n  in
                 match uu____16428 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16438 ->
                     let uu____16451 =
                       FStar_List.fold_right
                         (fun uu____16482  ->
                            fun uu____16483  ->
                              match uu____16483 with
                              | (bs,guard1) ->
                                  let uu____16510 =
                                    let uu____16523 =
                                      let uu____16524 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16524
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16523
                                     in
                                  (match uu____16510 with
                                   | (t,uu____16541,g) ->
                                       let uu____16555 =
                                         let uu____16558 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16558 :: bs  in
                                       let uu____16559 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16555, uu____16559))) args
                         ([], guard)
                        in
                     (match uu____16451 with
                      | (bs,guard1) ->
                          let uu____16576 =
                            let uu____16583 =
                              let uu____16596 =
                                let uu____16597 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16597
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16596
                               in
                            match uu____16583 with
                            | (t,uu____16614,g) ->
                                let uu____16628 = FStar_Options.ml_ish ()  in
                                if uu____16628
                                then
                                  let uu____16637 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16640 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16637, uu____16640)
                                else
                                  (let uu____16645 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16648 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16645, uu____16648))
                             in
                          (match uu____16576 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16667 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16667
                                 then
                                   let uu____16671 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16673 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16675 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16671 uu____16673 uu____16675
                                 else ());
                                (let g =
                                   let uu____16681 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16681
                                    in
                                 let uu____16682 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16682))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16683;
                        FStar_Syntax_Syntax.pos = uu____16684;
                        FStar_Syntax_Syntax.vars = uu____16685;_},uu____16686)
                     ->
                     let uu____16723 =
                       FStar_List.fold_right
                         (fun uu____16754  ->
                            fun uu____16755  ->
                              match uu____16755 with
                              | (bs,guard1) ->
                                  let uu____16782 =
                                    let uu____16795 =
                                      let uu____16796 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16796
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16795
                                     in
                                  (match uu____16782 with
                                   | (t,uu____16813,g) ->
                                       let uu____16827 =
                                         let uu____16830 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16830 :: bs  in
                                       let uu____16831 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16827, uu____16831))) args
                         ([], guard)
                        in
                     (match uu____16723 with
                      | (bs,guard1) ->
                          let uu____16848 =
                            let uu____16855 =
                              let uu____16868 =
                                let uu____16869 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16869
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16868
                               in
                            match uu____16855 with
                            | (t,uu____16886,g) ->
                                let uu____16900 = FStar_Options.ml_ish ()  in
                                if uu____16900
                                then
                                  let uu____16909 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16912 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16909, uu____16912)
                                else
                                  (let uu____16917 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16920 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16917, uu____16920))
                             in
                          (match uu____16848 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16939 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16939
                                 then
                                   let uu____16943 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16945 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16947 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16943 uu____16945 uu____16947
                                 else ());
                                (let g =
                                   let uu____16953 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16953
                                    in
                                 let uu____16954 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16954))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____16977 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____16977 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____16999 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____16999)  in
                          ((let uu____17001 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17001
                            then
                              let uu____17004 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17006 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17008 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17011 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17004 uu____17006 uu____17008
                                uu____17011
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17057) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17063,uu____17064) ->
                     check_function_app t guard
                 | uu____17105 ->
                     let uu____17106 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17106
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
                  let uu____17189 =
                    FStar_List.fold_left2
                      (fun uu____17258  ->
                         fun uu____17259  ->
                           fun uu____17260  ->
                             match (uu____17258, uu____17259, uu____17260)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17413 =
                                     let uu____17415 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17415 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17413
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17421 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17421 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17450 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17450 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17455 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17455)
                                              &&
                                              (let uu____17458 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____17458))
                                          in
                                       let uu____17460 =
                                         let uu____17471 =
                                           let uu____17482 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17482]  in
                                         FStar_List.append seen uu____17471
                                          in
                                       let uu____17515 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17460, uu____17515, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17189 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17583 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17583
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____17586 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17586 with | (c2,g) -> (e, c2, g)))
              | uu____17603 ->
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
            let uu____17694 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17694 with
            | (head1,args) ->
                let uu____17737 =
                  let uu____17738 = FStar_Syntax_Subst.compress head1  in
                  uu____17738.FStar_Syntax_Syntax.n  in
                (match uu____17737 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____17742;
                        FStar_Syntax_Syntax.vars = uu____17743;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____17750 ->
                     if norm1
                     then t1
                     else
                       (let uu____17754 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____17754))
          
          and unfold_once t f us args =
            let uu____17772 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____17772
            then t
            else
              (let uu____17777 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____17777 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____17797 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____17797 with
                    | (uu____17802,head_def) ->
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
          let uu____17809 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____17809  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____17828 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____17828
           then
             let uu____17833 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____17835 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____17833 uu____17835
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____17855 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____17857 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____17855 uu____17857 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____17861 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____17861 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____17905 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____17905 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____17906;
                    FStar_Syntax_Syntax.pos = uu____17907;
                    FStar_Syntax_Syntax.vars = uu____17908;_} ->
                    let uu____17911 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____17911 with
                     | (head_p,args_p) ->
                         let uu____17954 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____17954
                         then
                           let uu____17957 =
                             let uu____17958 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____17958.FStar_Syntax_Syntax.n  in
                           (match uu____17957 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____17963 =
                                    let uu____17965 =
                                      let uu____17967 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____17967
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____17965
                                     in
                                  if uu____17963
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____17995 =
                                    let uu____18020 =
                                      let uu____18024 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18024
                                       in
                                    match uu____18020 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18073 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18073 with
                                         | (params_p,uu____18131) ->
                                             let uu____18172 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18172 with
                                              | (params_s,uu____18230) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____17995 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18359  ->
                                             fun uu____18360  ->
                                               match (uu____18359,
                                                       uu____18360)
                                               with
                                               | ((p,uu____18394),(s,uu____18396))
                                                   ->
                                                   let uu____18429 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18429 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18432 =
                                                          let uu____18434 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18436 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18434
                                                            uu____18436
                                                           in
                                                        fail2 uu____18432
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
                            | uu____18441 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18445 =
                              let uu____18447 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18449 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18447 uu____18449
                               in
                            fail2 uu____18445))
                | uu____18452 ->
                    let uu____18453 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18453 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18490 = FStar_Syntax_Util.head_and_args e  in
          match uu____18490 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18554 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18554 with
                    | (us,t_f) ->
                        let uu____18571 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18571 with
                         | (formals,t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18700 formals1 args1 =
                                 match uu____18700 with
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
                                          let uu____18845 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____18845, bvs, guard)
                                      | ((f1,uu____18851)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____18909 =
                                            let uu____18930 =
                                              let uu____18931 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____18931.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18930 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2424_18956 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2424_18956.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2424_18956.FStar_Syntax_Syntax.index);
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
                                                uu____18979 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____18993 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____18993 with
                                                 | (a1,uu____19021,g) ->
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
                                            | uu____19045 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____18909 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19107 =
                                                 let uu____19130 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19130)
                                                  in
                                               aux uu____19107 formals2 args2)
                                      | uu____19169 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19225 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19274 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19274
           then
             let uu____19279 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19281 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19279
               uu____19281
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19296 ->
               let uu____19303 =
                 let uu____19305 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19305
                  in
               failwith uu____19303
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2456_19320 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2456_19320.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2456_19320.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19321 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19321,
                 (let uu___2459_19325 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2459_19325.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2463_19328 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2463_19328.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2463_19328.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19329 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19329,
                 (let uu___2466_19333 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2466_19333.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19334 ->
               let uu____19335 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19335 with
                | (uu____19357,e_c,uu____19359,uu____19360) ->
                    let uu____19365 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19365 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____19388 =
                              let uu____19390 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t
                                 in
                              Prims.op_Negation uu____19390  in
                            if uu____19388
                            then
                              let uu____19393 =
                                let uu____19395 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____19397 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19395 uu____19397
                                 in
                              fail1 uu____19393
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19455  ->
                        match uu____19455 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19485
                                 -> (p1, b)
                             | uu____19495 ->
                                 let uu____19496 =
                                   let uu____19499 =
                                     let uu____19500 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____19500
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____19499
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____19496, b))) sub_pats
                    in
                 let uu___2494_19504 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2494_19504.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19549  ->
                         match uu____19549 with
                         | (x,uu____19559) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19567
                                  -> false
                              | uu____19575 -> true)))
                  in
               let uu____19577 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____19577 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19614 =
                          let uu____19616 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____19618 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____19620 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____19627 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19616 uu____19618 uu____19620 uu____19627
                           in
                        failwith uu____19614)
                     else ();
                     (let uu____19632 =
                        let uu____19641 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____19641 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard) ->
                            let g' =
                              let uu____19669 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____19669  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____19672 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____19672
                              then
                                let uu____19677 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____19679 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____19681 =
                                  let uu____19683 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____19691 =
                                           let uu____19693 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____19695 =
                                             let uu____19697 =
                                               let uu____19699 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____19699 ")"
                                                in
                                             Prims.op_Hat " : " uu____19697
                                              in
                                           Prims.op_Hat uu____19693
                                             uu____19695
                                            in
                                         Prims.op_Hat "(" uu____19691)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____19683
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19677 uu____19679 uu____19681
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1))
                         in
                      match uu____19632 with
                      | (simple_pat_e1,simple_bvs1,g1) ->
                          let uu____19731 =
                            let uu____19753 =
                              let uu____19775 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], uu____19775)  in
                            FStar_List.fold_left2
                              (fun uu____19836  ->
                                 fun uu____19837  ->
                                   fun x  ->
                                     match (uu____19836, uu____19837) with
                                     | ((env2,bvs,pats,subst1,g),(p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____19970 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____19970 with
                                          | (bvs_p,e_p,p2,g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let uu____20011 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20011))) uu____19753
                              sub_pats1 simple_bvs1
                             in
                          (match uu____19731 with
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
                                              let uu___2566_20223 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2566_20223.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____20228 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____20228
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____20272)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20309 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____20309
                                             | uu____20329 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20355 ->
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
                                     let uu___2587_20398 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2587_20398.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20410 -> failwith "Impossible"  in
                               let uu____20414 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, pat_e, uu____20414, g))))))
           in
        (let uu____20418 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____20418
         then
           let uu____20423 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20423
         else ());
        (let uu____20428 =
           let uu____20439 =
             let uu___2592_20440 =
               let uu____20441 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____20441 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2592_20440.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2592_20440.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2592_20440.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2592_20440.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2592_20440.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2592_20440.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2592_20440.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2592_20440.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2592_20440.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2592_20440.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2592_20440.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2592_20440.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2592_20440.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2592_20440.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2592_20440.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2592_20440.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2592_20440.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2592_20440.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2592_20440.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2592_20440.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2592_20440.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2592_20440.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2592_20440.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2592_20440.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2592_20440.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2592_20440.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2592_20440.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2592_20440.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2592_20440.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2592_20440.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2592_20440.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2592_20440.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2592_20440.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2592_20440.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2592_20440.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2592_20440.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2592_20440.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2592_20440.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2592_20440.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2592_20440.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2592_20440.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2592_20440.FStar_TypeChecker_Env.nbe)
             }  in
           let uu____20457 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____20439 uu____20457 pat_t  in
         match uu____20428 with
         | (bvs,pat_e,pat,g) ->
             ((let uu____20481 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____20481
               then
                 let uu____20486 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____20488 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20486
                   uu____20488
               else ());
              (let uu____20493 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____20494 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, uu____20493, pat_e, uu____20494, g))))

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
        let uu____20540 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____20540 with
        | (pattern,when_clause,branch_exp) ->
            let uu____20586 = branch1  in
            (match uu____20586 with
             | (cpat,uu____20628,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____20650 =
                   let uu____20657 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____20657
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____20650 with
                  | (scrutinee_env,uu____20691) ->
                      let uu____20696 = tc_pat env pat_t pattern  in
                      (match uu____20696 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp,guard_pat)
                           ->
                           let uu____20747 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____20777 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____20777
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____20800 =
                                      let uu____20807 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____20807 e  in
                                    match uu____20800 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____20747 with
                            | (when_clause1,g_when) ->
                                let uu____20861 = tc_term pat_env branch_exp
                                   in
                                (match uu____20861 with
                                 | (branch_exp1,c,g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____20917 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _20928  ->
                                                  FStar_Pervasives_Native.Some
                                                    _20928) uu____20917
                                          in
                                       let uu____20929 =
                                         let eqs =
                                           let uu____20951 =
                                             let uu____20953 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____20953
                                              in
                                           if uu____20951
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____20969 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____20984 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____20987 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____20990 ->
                                                  let uu____20991 =
                                                    let uu____20994 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____20994 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____20991)
                                            in
                                         let uu____20997 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch
                                            in
                                         match uu____20997 with
                                         | (c1,g_branch1) ->
                                             let uu____21024 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____21041 when
                                                   let uu____21054 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____21054
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
                                                   let uu____21085 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____21086 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____21085, uu____21086)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____21107 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21107
                                                      in
                                                   let uu____21108 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____21109 =
                                                     let uu____21110 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21110 g_when
                                                      in
                                                   (uu____21108, uu____21109)
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
                                                   let uu____21128 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____21128, g_when)
                                                in
                                             (match uu____21024 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21171 =
                                                        should_return1 &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____21171
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____21176 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  let uu____21177 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21176, uu____21177))
                                          in
                                       match uu____20929 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21228 =
                                               let uu____21230 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____21230
                                                in
                                             if uu____21228
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21284 =
                                                      let uu____21292 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21292
                                                       in
                                                    match uu____21284 with
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
                                                          let uu____21308 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator
                                                             in
                                                          (match uu____21308
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> []
                                                           | uu____21329 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let disc1 =
                                                                 let uu____21345
                                                                   =
                                                                   let uu____21350
                                                                    =
                                                                    let uu____21351
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____21351]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21350
                                                                    in
                                                                 uu____21345
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let uu____21376
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool
                                                                  in
                                                               [uu____21376])
                                                        else []
                                                     in
                                                  let fail1 uu____21384 =
                                                    let uu____21385 =
                                                      let uu____21387 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____21389 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____21391 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21387
                                                        uu____21389
                                                        uu____21391
                                                       in
                                                    failwith uu____21385  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____21406) ->
                                                        head_constructor t1
                                                    | uu____21411 -> fail1 ()
                                                     in
                                                  let force_scrutinee
                                                    uu____21417 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____21418 =
                                                          let uu____21420 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p
                                                             in
                                                          let uu____21422 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2
                                                             in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21420
                                                            uu____21422
                                                           in
                                                        failwith uu____21418
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t
                                                     in
                                                  let pat_exp2 =
                                                    let uu____21429 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____21429
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21434,FStar_Syntax_Syntax.Tm_name
                                                     uu____21435) -> []
                                                  | (uu____21436,FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     )) -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21439 =
                                                        let uu____21440 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        let uu____21441 =
                                                          force_scrutinee ()
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21440
                                                          uu____21441
                                                          pat_exp2
                                                         in
                                                      [uu____21439]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21442,FStar_Pervasives_Native.Some
                                                      uu____21443)),uu____21444)
                                                      ->
                                                      let uu____21461 =
                                                        let uu____21468 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env
                                                           in
                                                        match uu____21468
                                                        with
                                                        | (env1,uu____21482)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2
                                                         in
                                                      (match uu____21461 with
                                                       | (uu____21489,t,uu____21491)
                                                           ->
                                                           let uu____21492 =
                                                             let uu____21493
                                                               =
                                                               force_scrutinee
                                                                 ()
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21493
                                                               pat_exp2
                                                              in
                                                           [uu____21492])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21494,[]),FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21495) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21519 =
                                                        let uu____21521 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21521
                                                         in
                                                      if uu____21519
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21531 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21534 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21531
                                                           uu____21534)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21537,[]),FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21538) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21556 =
                                                        let uu____21558 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21558
                                                         in
                                                      if uu____21556
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21568 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21571 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21568
                                                           uu____21571)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21574,pat_args),FStar_Syntax_Syntax.Tm_app
                                                     (head1,args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____21621 =
                                                        (let uu____21625 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____21625)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args))
                                                         in
                                                      if uu____21621
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21653 =
                                                             let uu____21658
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____21658
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____21744
                                                                     ->
                                                                    match uu____21744
                                                                    with
                                                                    | 
                                                                    ((pi,uu____21766),
                                                                    (ei,uu____21768))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____21796
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____21796
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____21817
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____21829
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____21829
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____21831
                                                                    =
                                                                    let uu____21832
                                                                    =
                                                                    let uu____21837
                                                                    =
                                                                    let uu____21838
                                                                    =
                                                                    let uu____21847
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____21847
                                                                     in
                                                                    [uu____21838]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____21837
                                                                     in
                                                                    uu____21832
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____21831
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____21653
                                                             FStar_List.flatten
                                                            in
                                                         let uu____21870 =
                                                           let uu____21873 =
                                                             force_scrutinee
                                                               ()
                                                              in
                                                           discriminate
                                                             uu____21873 f
                                                            in
                                                         FStar_List.append
                                                           uu____21870
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____21876,uu____21877)
                                                      -> []
                                                  | uu____21884 ->
                                                      let uu____21889 =
                                                        let uu____21891 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2
                                                           in
                                                        let uu____21893 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2
                                                           in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____21891
                                                          uu____21893
                                                         in
                                                      failwith uu____21889
                                                   in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____21922 =
                                                    let uu____21924 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____21924
                                                     in
                                                  if uu____21922
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____21930 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____21930
                                                        in
                                                     let uu____21939 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____21939 with
                                                     | (k,uu____21945) ->
                                                         let uu____21946 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____21946
                                                          with
                                                          | (t1,uu____21954,uu____21955)
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
                                           ((let uu____21967 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____21967
                                             then
                                               let uu____21970 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____21970
                                             else ());
                                            (let uu____21976 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____21993 =
                                               let uu____21994 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____21994 guard
                                                in
                                             (uu____21976, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____21993))))))))))

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
          let uu____22041 = check_let_bound_def true env1 lb  in
          (match uu____22041 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____22067 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____22089 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____22089, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22095 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____22095
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____22096 =
                      let uu____22109 =
                        let uu____22124 =
                          let uu____22133 =
                            let uu____22140 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____22140)
                             in
                          [uu____22133]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____22124
                         in
                      FStar_List.hd uu____22109  in
                    match uu____22096 with
                    | (uu____22176,univs1,e11,c11,gvs) ->
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
                        let uu____22190 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____22190))
                  in
               (match uu____22067 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____22207 =
                      let uu____22216 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____22216
                      then
                        let uu____22227 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____22227 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22261 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____22261
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22262 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____22262, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____22277 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____22277
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____22283 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____22283
                            then e2
                            else
                              ((let uu____22291 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____22291
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
                    (match uu____22207 with
                     | (e21,c12) ->
                         ((let uu____22315 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____22315
                           then
                             let uu____22318 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22318
                           else ());
                          (let e12 =
                             let uu____22324 = FStar_Options.tcnorm ()  in
                             if uu____22324
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
                           (let uu____22330 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____22330
                            then
                              let uu____22333 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22333
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
                            let uu____22342 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____22356 =
                              FStar_Syntax_Util.lcomp_of_comp cres  in
                            (uu____22342, uu____22356,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22357 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____22368 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____22368
        then
          let universe_of_binders bs =
            let uu____22395 =
              FStar_List.fold_left
                (fun uu____22420  ->
                   fun b  ->
                     match uu____22420 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____22395 with | (uu____22468,us) -> FStar_List.rev us
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
            let uu___2904_22504 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2904_22504.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2904_22504.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2904_22504.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2904_22504.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2904_22504.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2904_22504.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2904_22504.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2904_22504.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2904_22504.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2904_22504.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2904_22504.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2904_22504.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2904_22504.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2904_22504.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2904_22504.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2904_22504.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2904_22504.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2904_22504.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2904_22504.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2904_22504.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2904_22504.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2904_22504.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2904_22504.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2904_22504.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2904_22504.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2904_22504.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2904_22504.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2904_22504.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2904_22504.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2904_22504.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2904_22504.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2904_22504.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2904_22504.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2904_22504.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2904_22504.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2904_22504.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2904_22504.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2904_22504.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2904_22504.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2904_22504.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2904_22504.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2904_22504.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____22506 =
            let uu____22518 =
              let uu____22519 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____22519 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____22518 lb  in
          (match uu____22506 with
           | (e1,uu____22542,c1,g1,annotated) ->
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
                  (let uu____22556 =
                     let uu____22562 =
                       let uu____22564 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____22566 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____22564 uu____22566
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____22562)
                      in
                   FStar_Errors.raise_error uu____22556
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____22577 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_Syntax_Syntax.res_typ)
                      in
                   if uu____22577
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___2919_22589 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2919_22589.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2919_22589.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____22590 =
                   let uu____22595 =
                     let uu____22596 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____22596]  in
                   FStar_Syntax_Subst.open_term uu____22595 e2  in
                 match uu____22590 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____22640 = tc_term env_x e21  in
                     (match uu____22640 with
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
                            let uu____22666 =
                              let uu____22673 =
                                let uu____22674 =
                                  let uu____22688 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____22688)  in
                                FStar_Syntax_Syntax.Tm_let uu____22674  in
                              FStar_Syntax_Syntax.mk uu____22673  in
                            uu____22666 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____22706 =
                              let uu____22707 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____22708 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____22707
                                c1.FStar_Syntax_Syntax.res_typ uu____22708
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _22709  ->
                                 FStar_TypeChecker_Common.NonTrivial _22709)
                              uu____22706
                             in
                          let g21 =
                            let uu____22711 =
                              let uu____22712 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____22712 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____22711
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____22715 =
                            let uu____22717 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____22717  in
                          if uu____22715
                          then
                            let tt =
                              let uu____22728 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____22728
                                FStar_Option.get
                               in
                            ((let uu____22734 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____22734
                              then
                                let uu____22739 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____22741 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____22739 uu____22741
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____22748 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____22748 with
                             | (t,g_ex) ->
                                 ((let uu____22762 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____22762
                                   then
                                     let uu____22767 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____22769 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____22767 uu____22769
                                   else ());
                                  (let uu____22774 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___2952_22776 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___2952_22776.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___2952_22776.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___2952_22776.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____22774))))))))
      | uu____22777 ->
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
          let uu____22813 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____22813 with
           | (lbs1,e21) ->
               let uu____22832 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____22832 with
                | (env0,topt) ->
                    let uu____22851 = build_let_rec_env true env0 lbs1  in
                    (match uu____22851 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____22874 = check_let_recs rec_env lbs2  in
                         (match uu____22874 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____22894 =
                                  let uu____22895 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____22895
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____22894
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____22901 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____22901
                                  (fun _22918  ->
                                     FStar_Pervasives_Native.Some _22918)
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
                                     let uu____22955 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____22989 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____22989)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____22955
                                      in
                                   FStar_List.map2
                                     (fun uu____23024  ->
                                        fun lb  ->
                                          match uu____23024 with
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
                                let uu____23072 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____23072
                                 in
                              let uu____23073 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____23073 with
                               | (lbs5,e22) ->
                                   ((let uu____23093 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____23093
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23094 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____23094, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23108 -> failwith "Impossible"

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
          let uu____23144 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23144 with
           | (lbs1,e21) ->
               let uu____23163 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23163 with
                | (env0,topt) ->
                    let uu____23182 = build_let_rec_env false env0 lbs1  in
                    (match uu____23182 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23205 =
                           let uu____23212 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____23212
                             (fun uu____23235  ->
                                match uu____23235 with
                                | (lbs3,g) ->
                                    let uu____23254 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____23254))
                            in
                         (match uu____23205 with
                          | (lbs3,g_lbs) ->
                              let uu____23269 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3027_23292 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3027_23292.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3027_23292.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3030_23294 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3030_23294.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____23269 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____23321 = tc_term env2 e21  in
                                   (match uu____23321 with
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
                                          let uu____23345 =
                                            let uu____23346 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23346 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23345
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
                                          let uu___3051_23356 = cres4  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___3051_23356.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___3051_23356.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___3051_23356.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____23364 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____23364))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____23365 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____23365 with
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
                                                  uu____23406 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____23407 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____23407 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3067_23421
                                                           = cres5  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___3067_23421.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___3067_23421.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___3067_23421.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____23422 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____23422))))))))))
      | uu____23423 -> failwith "Impossible"

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
          let uu____23471 = FStar_Options.ml_ish ()  in
          if uu____23471
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____23479 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____23479 with
             | (formals,c) ->
                 let uu____23511 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____23511 with
                  | (actuals,uu____23522,uu____23523) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____23544 =
                          let uu____23550 =
                            let uu____23552 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____23554 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____23552 uu____23554
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____23550)
                           in
                        FStar_Errors.raise_error uu____23544
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____23562 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____23562 actuals
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
                                (let uu____23593 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____23593)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____23612 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____23612)
                               in
                            let msg =
                              let uu____23617 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____23619 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____23617 uu____23619 formals_msg
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
        let uu____23631 =
          FStar_List.fold_left
            (fun uu____23664  ->
               fun lb  ->
                 match uu____23664 with
                 | (lbs1,env1,g_acc) ->
                     let uu____23689 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____23689 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____23712 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____23731 =
                                 let uu____23738 =
                                   let uu____23739 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____23739
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3113_23750 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3113_23750.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3113_23750.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3113_23750.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3113_23750.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3113_23750.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3113_23750.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3113_23750.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3113_23750.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3113_23750.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3113_23750.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3113_23750.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3113_23750.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3113_23750.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3113_23750.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3113_23750.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3113_23750.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3113_23750.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3113_23750.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3113_23750.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3113_23750.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3113_23750.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3113_23750.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3113_23750.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3113_23750.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3113_23750.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3113_23750.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3113_23750.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3113_23750.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3113_23750.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3113_23750.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3113_23750.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3113_23750.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3113_23750.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3113_23750.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3113_23750.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3113_23750.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3113_23750.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3113_23750.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3113_23750.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3113_23750.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3113_23750.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3113_23750.FStar_TypeChecker_Env.nbe)
                                    }) t uu____23738
                                  in
                               match uu____23731 with
                               | (t1,uu____23759,g) ->
                                   let uu____23761 =
                                     let uu____23762 =
                                       let uu____23763 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____23763
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____23762
                                      in
                                   let uu____23764 = norm env01 t1  in
                                   (uu____23761, uu____23764))
                             in
                          (match uu____23712 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____23784 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____23784
                                 then
                                   let uu___3123_23787 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3123_23787.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3123_23787.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3123_23787.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3123_23787.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3123_23787.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3123_23787.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3123_23787.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3123_23787.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3123_23787.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3123_23787.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3123_23787.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3123_23787.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3123_23787.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3123_23787.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3123_23787.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3123_23787.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3123_23787.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3123_23787.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3123_23787.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3123_23787.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3123_23787.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3123_23787.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3123_23787.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3123_23787.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3123_23787.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3123_23787.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3123_23787.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3123_23787.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3123_23787.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3123_23787.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3123_23787.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3123_23787.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3123_23787.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3123_23787.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3123_23787.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3123_23787.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3123_23787.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3123_23787.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3123_23787.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3123_23787.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3123_23787.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3123_23787.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3126_23801 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3126_23801.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3126_23801.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3126_23801.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3126_23801.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____23631 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____23827 =
        let uu____23836 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____23862 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____23862 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____23892 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____23892
                       | uu____23899 ->
                           let lb1 =
                             let uu___3143_23902 = lb  in
                             let uu____23903 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____23903;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3143_23902.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____23906 =
                             let uu____23913 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____23913
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____23906 with
                            | (e,c,g) ->
                                ((let uu____23922 =
                                    let uu____23924 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____23924  in
                                  if uu____23922
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
        FStar_All.pipe_right uu____23836 FStar_List.unzip  in
      match uu____23827 with
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
        let uu____23980 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____23980 with
        | (env1,uu____23999) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____24007 = check_lbtyp top_level env lb  in
            (match uu____24007 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____24056 =
                     tc_maybe_toplevel_term
                       (let uu___3174_24065 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3174_24065.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3174_24065.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3174_24065.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3174_24065.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3174_24065.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3174_24065.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3174_24065.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3174_24065.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3174_24065.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3174_24065.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3174_24065.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3174_24065.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3174_24065.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3174_24065.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3174_24065.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3174_24065.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3174_24065.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3174_24065.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3174_24065.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3174_24065.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3174_24065.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3174_24065.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3174_24065.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3174_24065.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3174_24065.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3174_24065.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3174_24065.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3174_24065.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3174_24065.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3174_24065.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3174_24065.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3174_24065.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3174_24065.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3174_24065.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3174_24065.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3174_24065.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3174_24065.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3174_24065.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3174_24065.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3174_24065.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3174_24065.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3174_24065.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____24056 with
                   | (e12,c1,g1) ->
                       let uu____24080 =
                         let uu____24085 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24091  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____24085 e12 c1 wf_annot
                          in
                       (match uu____24080 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____24108 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____24108
                              then
                                let uu____24111 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____24113 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____24115 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24111 uu____24113 uu____24115
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
            let uu____24154 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24154 with
             | (univ_opening,univ_vars1) ->
                 let uu____24187 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24187))
        | uu____24192 ->
            let uu____24193 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24193 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24243 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24243)
                 else
                   (let uu____24250 = FStar_Syntax_Util.type_u ()  in
                    match uu____24250 with
                    | (k,uu____24270) ->
                        let uu____24271 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____24271 with
                         | (t2,uu____24293,g) ->
                             ((let uu____24296 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____24296
                               then
                                 let uu____24299 =
                                   let uu____24301 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____24301
                                    in
                                 let uu____24302 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24299 uu____24302
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____24308 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24308))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____24314  ->
      match uu____24314 with
      | (x,imp) ->
          let uu____24341 = FStar_Syntax_Util.type_u ()  in
          (match uu____24341 with
           | (tu,u) ->
               ((let uu____24363 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____24363
                 then
                   let uu____24366 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____24368 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____24370 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____24366 uu____24368 uu____24370
                 else ());
                (let uu____24375 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____24375 with
                 | (t,uu____24397,g) ->
                     let uu____24399 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____24415 = tc_tactic env tau  in
                           (match uu____24415 with
                            | (tau1,uu____24429,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____24433 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____24399 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3236_24468 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3236_24468.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3236_24468.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____24470 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____24470
                            then
                              let uu____24473 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____24477 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____24473
                                uu____24477
                            else ());
                           (let uu____24482 = push_binding env x1  in
                            (x1, uu____24482, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____24494 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____24494
       then
         let uu____24497 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____24497
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____24610 = tc_binder env1 b  in
             (match uu____24610 with
              | (b1,env',g,u) ->
                  let uu____24659 = aux env' bs2  in
                  (match uu____24659 with
                   | (bs3,env'1,g',us) ->
                       let uu____24720 =
                         let uu____24721 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____24721  in
                       ((b1 :: bs3), env'1, uu____24720, (u :: us))))
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
          (fun uu____24829  ->
             fun uu____24830  ->
               match (uu____24829, uu____24830) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____24922 = tc_term en1 t  in
                     match uu____24922 with
                     | (t1,uu____24942,g') ->
                         let uu____24944 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____24944)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____24998  ->
             match uu____24998 with
             | (pats1,g) ->
                 let uu____25025 = tc_args en p  in
                 (match uu____25025 with
                  | (args,g') ->
                      let uu____25038 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____25038))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____25051 = tc_maybe_toplevel_term env e  in
      match uu____25051 with
      | (e1,c,g) ->
          let uu____25067 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____25067
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____25081 =
               let uu____25087 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____25087
               then
                 let uu____25095 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____25095, false)
               else
                 (let uu____25100 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____25100, true))
                in
             match uu____25081 with
             | (target_comp,allow_ghost) ->
                 let uu____25113 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____25113 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____25123 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____25124 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____25123, uu____25124)
                  | uu____25125 ->
                      if allow_ghost
                      then
                        let uu____25135 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____25135
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____25149 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____25149
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
      let uu____25173 = tc_tot_or_gtot_term env t  in
      match uu____25173 with
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
      (let uu____25206 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25206
       then
         let uu____25211 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____25211
       else ());
      (let env1 =
         let uu___3318_25217 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3318_25217.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3318_25217.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3318_25217.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3318_25217.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3318_25217.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3318_25217.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3318_25217.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3318_25217.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3318_25217.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3318_25217.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3318_25217.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3318_25217.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3318_25217.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3318_25217.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3318_25217.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3318_25217.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3318_25217.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3318_25217.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3318_25217.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3318_25217.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3318_25217.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3318_25217.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3318_25217.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3318_25217.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3318_25217.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3318_25217.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3318_25217.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3318_25217.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3318_25217.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3318_25217.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3318_25217.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3318_25217.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3318_25217.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3318_25217.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3318_25217.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3318_25217.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3318_25217.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3318_25217.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3318_25217.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3318_25217.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3318_25217.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____25225 =
         try
           (fun uu___3322_25239  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____25260) ->
             let uu____25263 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____25263
          in
       match uu____25225 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____25281 = FStar_Syntax_Util.is_total_lcomp c1  in
           if uu____25281
           then (t, (c1.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____25292 =
                let uu____25298 =
                  let uu____25300 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25300
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25298)
                 in
              let uu____25304 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____25292 uu____25304))
  
let level_of_type_fail :
  'Auu____25320 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25320
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____25338 =
          let uu____25344 =
            let uu____25346 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____25346 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25344)  in
        let uu____25350 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____25338 uu____25350
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____25384 =
            let uu____25385 = FStar_Syntax_Util.unrefine t1  in
            uu____25385.FStar_Syntax_Syntax.n  in
          match uu____25384 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____25389 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____25395 = FStar_Syntax_Util.type_u ()  in
                 match uu____25395 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3354_25403 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3354_25403.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3354_25403.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3354_25403.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3354_25403.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3354_25403.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3354_25403.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3354_25403.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3354_25403.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3354_25403.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3354_25403.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3354_25403.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3354_25403.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3354_25403.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3354_25403.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3354_25403.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3354_25403.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3354_25403.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3354_25403.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3354_25403.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3354_25403.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3354_25403.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3354_25403.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3354_25403.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3354_25403.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3354_25403.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3354_25403.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3354_25403.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3354_25403.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3354_25403.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3354_25403.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3354_25403.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3354_25403.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3354_25403.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3354_25403.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3354_25403.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3354_25403.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3354_25403.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3354_25403.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3354_25403.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3354_25403.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3354_25403.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3354_25403.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25408 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____25408
                       | uu____25410 ->
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
      let uu____25427 =
        let uu____25428 = FStar_Syntax_Subst.compress e  in
        uu____25428.FStar_Syntax_Syntax.n  in
      match uu____25427 with
      | FStar_Syntax_Syntax.Tm_bvar uu____25431 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____25434 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____25458 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____25475) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____25520) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____25527 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25527 with | ((uu____25536,t),uu____25538) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____25544 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____25544
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25547,(FStar_Util.Inl t,uu____25549),uu____25550) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25597,(FStar_Util.Inr c,uu____25599),uu____25600) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____25648 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____25657;
             FStar_Syntax_Syntax.vars = uu____25658;_},us)
          ->
          let uu____25664 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25664 with
           | ((us',t),uu____25675) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____25682 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____25682)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____25701 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____25703 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____25712) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____25739 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____25739 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____25759  ->
                      match uu____25759 with
                      | (b,uu____25767) ->
                          let uu____25772 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____25772) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____25777 = universe_of_aux env res  in
                 level_of_type env res uu____25777  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____25888 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____25904 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____25942 ->
                let uu____25943 = universe_of_aux env hd3  in
                (uu____25943, args1)
            | FStar_Syntax_Syntax.Tm_name uu____25954 ->
                let uu____25955 = universe_of_aux env hd3  in
                (uu____25955, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____25966 ->
                let uu____25979 = universe_of_aux env hd3  in
                (uu____25979, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____25990 ->
                let uu____25997 = universe_of_aux env hd3  in
                (uu____25997, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____26008 ->
                let uu____26035 = universe_of_aux env hd3  in
                (uu____26035, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____26046 ->
                let uu____26053 = universe_of_aux env hd3  in
                (uu____26053, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____26064 ->
                let uu____26065 = universe_of_aux env hd3  in
                (uu____26065, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____26076 ->
                let uu____26091 = universe_of_aux env hd3  in
                (uu____26091, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26102 ->
                let uu____26109 = universe_of_aux env hd3  in
                (uu____26109, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26120 ->
                let uu____26121 = universe_of_aux env hd3  in
                (uu____26121, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26132,hd4::uu____26134) ->
                let uu____26199 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____26199 with
                 | (uu____26214,uu____26215,hd5) ->
                     let uu____26233 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____26233 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____26290 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____26292 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____26292 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____26350 ->
                let uu____26351 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____26351 with
                 | (env1,uu____26373) ->
                     let env2 =
                       let uu___3515_26379 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3515_26379.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3515_26379.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3515_26379.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3515_26379.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3515_26379.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3515_26379.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3515_26379.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3515_26379.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3515_26379.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3515_26379.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3515_26379.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3515_26379.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3515_26379.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3515_26379.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3515_26379.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3515_26379.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3515_26379.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3515_26379.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3515_26379.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3515_26379.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3515_26379.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3515_26379.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3515_26379.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3515_26379.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3515_26379.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3515_26379.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3515_26379.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3515_26379.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3515_26379.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3515_26379.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3515_26379.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3515_26379.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3515_26379.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3515_26379.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3515_26379.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3515_26379.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3515_26379.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3515_26379.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3515_26379.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3515_26379.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____26384 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____26384
                       then
                         let uu____26389 =
                           let uu____26391 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____26391  in
                         let uu____26392 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____26389 uu____26392
                       else ());
                      (let uu____26397 = tc_term env2 hd3  in
                       match uu____26397 with
                       | (uu____26418,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____26419;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____26421;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____26422;_},g)
                           ->
                           ((let uu____26436 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____26436 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____26447 = type_of_head true hd1 args  in
          (match uu____26447 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____26486 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____26486 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____26538 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____26538)))
      | FStar_Syntax_Syntax.Tm_match (uu____26540,hd1::uu____26542) ->
          let uu____26607 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____26607 with
           | (uu____26608,uu____26609,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____26627,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____26674 = universe_of_aux env e  in
      level_of_type env e uu____26674
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____26698 = tc_binders env tps  in
      match uu____26698 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____26756 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____26782 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26788 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____26788
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26790 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26790
            (fun uu____26804  ->
               match uu____26804 with
               | (t2,uu____26812) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26814;
             FStar_Syntax_Syntax.vars = uu____26815;_},us)
          ->
          let uu____26821 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26821
            (fun uu____26835  ->
               match uu____26835 with
               | (t2,uu____26843) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____26844) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____26846 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____26846
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____26848 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____26848
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____26853;_})
          ->
          let mk_comp =
            let uu____26897 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____26897
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____26928 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____26928
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____26998 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____26998
                 (fun u  ->
                    let uu____27006 =
                      let uu____27009 =
                        let uu____27016 =
                          let uu____27017 =
                            let uu____27032 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____27032)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____27017  in
                        FStar_Syntax_Syntax.mk uu____27016  in
                      uu____27009 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____27006))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27069 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27069 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27128 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____27128
                       (fun uc  ->
                          let uu____27136 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____27136)
                 | (x,imp)::bs3 ->
                     let uu____27162 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____27162
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27171 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27191) ->
          let uu____27196 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____27196
            (fun u_x  ->
               let uu____27204 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____27204)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27209;
             FStar_Syntax_Syntax.vars = uu____27210;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27289 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27289 with
           | (unary_op1,uu____27309) ->
               let head1 =
                 let uu____27337 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27337
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
             FStar_Syntax_Syntax.pos = uu____27385;
             FStar_Syntax_Syntax.vars = uu____27386;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27482 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27482 with
           | (unary_op1,uu____27502) ->
               let head1 =
                 let uu____27530 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____27530
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
             FStar_Syntax_Syntax.pos = uu____27586;
             FStar_Syntax_Syntax.vars = uu____27587;_},uu____27588::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____27627;
             FStar_Syntax_Syntax.vars = uu____27628;_},(t2,uu____27630)::uu____27631::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____27727 =
              let uu____27728 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____27728.FStar_Syntax_Syntax.n  in
            match uu____27727 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____27801 = FStar_Util.first_N n_args bs  in
                    match uu____27801 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____27889 =
                          let uu____27894 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____27894  in
                        (match uu____27889 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____27948 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____27948 with
                       | (bs1,c1) ->
                           let uu____27969 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____27969
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____28051  ->
                     match uu____28051 with
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
                         let uu____28127 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____28127)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____28129) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____28135,uu____28136) ->
                aux t2
            | uu____28177 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28178,(FStar_Util.Inl t2,uu____28180),uu____28181) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28228,(FStar_Util.Inr c,uu____28230),uu____28231) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____28296 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____28296
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____28304) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28309 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28332 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____28346 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____28357 = type_of_well_typed_term env t  in
      match uu____28357 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____28363;
            FStar_Syntax_Syntax.vars = uu____28364;_}
          -> FStar_Pervasives_Native.Some u
      | uu____28367 -> FStar_Pervasives_Native.None

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
            let uu___3794_28395 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3794_28395.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3794_28395.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3794_28395.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3794_28395.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3794_28395.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3794_28395.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3794_28395.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3794_28395.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3794_28395.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3794_28395.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3794_28395.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3794_28395.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3794_28395.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3794_28395.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3794_28395.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3794_28395.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3794_28395.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3794_28395.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3794_28395.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3794_28395.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3794_28395.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3794_28395.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3794_28395.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3794_28395.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3794_28395.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3794_28395.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3794_28395.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3794_28395.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3794_28395.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3794_28395.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3794_28395.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3794_28395.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3794_28395.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3794_28395.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3794_28395.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3794_28395.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3794_28395.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3794_28395.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3794_28395.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3794_28395.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3794_28395.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3794_28395.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28402 =
            if must_total
            then
              let uu____28404 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28404 with | (uu____28411,uu____28412,g) -> g
            else
              (let uu____28416 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28416 with | (uu____28423,uu____28424,g) -> g)
             in
          let uu____28426 = type_of_well_typed_term env2 t  in
          match uu____28426 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____28431 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____28431
                then
                  let uu____28436 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____28438 = FStar_Syntax_Print.term_to_string t  in
                  let uu____28440 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____28442 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____28436 uu____28438 uu____28440 uu____28442
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____28451 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____28451
                 then
                   let uu____28456 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____28458 = FStar_Syntax_Print.term_to_string t  in
                   let uu____28460 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____28462 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____28456
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____28458 uu____28460 uu____28462
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
            let uu___3825_28499 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3825_28499.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3825_28499.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3825_28499.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3825_28499.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3825_28499.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3825_28499.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3825_28499.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3825_28499.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3825_28499.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3825_28499.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3825_28499.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3825_28499.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3825_28499.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3825_28499.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3825_28499.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3825_28499.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3825_28499.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3825_28499.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3825_28499.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3825_28499.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3825_28499.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3825_28499.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3825_28499.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3825_28499.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3825_28499.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3825_28499.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3825_28499.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3825_28499.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3825_28499.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3825_28499.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3825_28499.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3825_28499.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3825_28499.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3825_28499.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3825_28499.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3825_28499.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3825_28499.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3825_28499.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3825_28499.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3825_28499.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3825_28499.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3825_28499.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28506 =
            if must_total
            then
              let uu____28508 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28508 with | (uu____28515,uu____28516,g) -> g
            else
              (let uu____28520 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28520 with | (uu____28527,uu____28528,g) -> g)
             in
          let uu____28530 =
            let uu____28532 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____28532  in
          if uu____28530
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  