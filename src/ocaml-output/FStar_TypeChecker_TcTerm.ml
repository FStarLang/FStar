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
              match copt with
              | FStar_Pervasives_Native.Some uu____761 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____764 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____767 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____767))
                     in
                  if uu____764
                  then
                    let uu____776 =
                      let uu____779 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____779  in
                    (uu____776, c)
                  else
                    (let uu____784 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____784
                     then
                       let uu____793 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____793)
                     else
                       (let uu____798 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____798
                        then
                          let uu____807 =
                            let uu____810 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____810  in
                          (uu____807, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____748 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____838 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____838
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____841 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low
                           in
                        if uu____841
                        then
                          let uu____845 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____847 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____849 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____845 uu____847 uu____849
                        else ());
                       (let uu____854 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____854 with
                        | (e1,uu____868,g) ->
                            let g1 =
                              let uu____871 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____871
                                "could not prove post-condition" g
                               in
                            ((let uu____874 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____874
                              then
                                let uu____877 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____879 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____877 uu____879
                              else ());
                             (let e2 =
                                FStar_TypeChecker_Util.maybe_lift env e1
                                  (FStar_Syntax_Util.comp_effect_name c4)
                                  (FStar_Syntax_Util.comp_effect_name
                                     expected_c)
                                  (FStar_Syntax_Util.comp_result c4)
                                 in
                              (e2, expected_c, g1)))))))
  
let no_logical_guard :
  'Auu____894 'Auu____895 .
    FStar_TypeChecker_Env.env ->
      ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____917  ->
      match uu____917 with
      | (te,kt,f) ->
          let uu____927 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____927 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____935 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____941 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____935 uu____941)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____954 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____954 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____959 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____959
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1001 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1001 with
        | (head1,args) ->
            let uu____1046 =
              let uu____1061 =
                let uu____1062 = FStar_Syntax_Util.un_uinst head1  in
                uu____1062.FStar_Syntax_Syntax.n  in
              (uu____1061, args)  in
            (match uu____1046 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1078) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1105,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1106))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1183,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1184))::(pat,FStar_Pervasives_Native.None
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
             | uu____1268 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1299 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1299) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1335 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1342 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1335 uu____1342  in
          let uu____1343 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1370  ->
                    match uu____1370 with
                    | (b,uu____1377) ->
                        let uu____1378 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1378))
             in
          match uu____1343 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1385) ->
              let uu____1390 =
                let uu____1396 =
                  let uu____1398 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1398
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1396)  in
              FStar_Errors.log_issue rng uu____1390
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1424 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1424 with
        | (head1,args) ->
            let uu____1469 =
              let uu____1484 =
                let uu____1485 = FStar_Syntax_Util.un_uinst head1  in
                uu____1485.FStar_Syntax_Syntax.n  in
              (uu____1484, args)  in
            (match uu____1469 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1501) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1523::(hd1,uu____1525)::(tl1,uu____1527)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1594 = pat_terms hd1  in
                 let uu____1597 = pat_terms tl1  in
                 FStar_List.append uu____1594 uu____1597
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1601::(pat,uu____1603)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1688 -> [])
         in
      let rec aux t1 =
        let uu____1713 =
          let uu____1714 = FStar_Syntax_Subst.compress t1  in
          uu____1714.FStar_Syntax_Syntax.n  in
        match uu____1713 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1719 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1720 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1721 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1722 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1735 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1736 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1737 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1756 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1771 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1778 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1801 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1815 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1838 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1846 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____1846 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____1879 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____1896  ->
                   match uu____1896 with
                   | (t3,uu____1908) ->
                       let uu____1913 = aux t3  in
                       FStar_List.append acc uu____1913) uu____1879 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1917,uu____1918) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1960) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____1966) -> aux t2  in
      let tlist =
        let uu____1974 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____1974 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = (Prims.parse_int "0")
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____1997 =
                    let uu____1999 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____1999  in
                  Prims.op_Hat s uu____1997) "" tlist
            in
         let uu____2003 =
           let uu____2009 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2009)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2003)
  
let check_smt_pat :
  'Auu____2024 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2024) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2065 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2065
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2068;
                  FStar_Syntax_Syntax.effect_name = uu____2069;
                  FStar_Syntax_Syntax.result_typ = uu____2070;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2074)::[];
                  FStar_Syntax_Syntax.flags = uu____2075;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2137 -> failwith "Impossible"
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
              let uu___345_2200 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___345_2200.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___345_2200.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___345_2200.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___345_2200.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___345_2200.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___345_2200.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___345_2200.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___345_2200.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___345_2200.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___345_2200.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___345_2200.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___345_2200.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___345_2200.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___345_2200.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___345_2200.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___345_2200.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___345_2200.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___345_2200.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___345_2200.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___345_2200.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___345_2200.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___345_2200.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___345_2200.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___345_2200.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___345_2200.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___345_2200.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___345_2200.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___345_2200.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___345_2200.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___345_2200.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___345_2200.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___345_2200.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___345_2200.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.postprocess =
                  (uu___345_2200.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___345_2200.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___345_2200.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___345_2200.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___345_2200.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___345_2200.FStar_TypeChecker_Env.nbe)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2226 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2226
               then
                 let uu____2229 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2232 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2229 uu____2232
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2266  ->
                         match uu____2266 with
                         | (b,uu____2276) ->
                             let t =
                               let uu____2282 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2282
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2285 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2286 -> []
                              | uu____2301 ->
                                  let uu____2302 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2302])))
                  in
               let as_lex_list dec =
                 let uu____2315 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2315 with
                 | (head1,uu____2335) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2363 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2371 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2380  ->
                         match uu___1_2380 with
                         | FStar_Syntax_Syntax.DECREASES uu____2382 -> true
                         | uu____2386 -> false))
                  in
               match uu____2371 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2393 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2414 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2443 =
              match uu____2443 with
              | (l,t,u_names) ->
                  let uu____2467 =
                    let uu____2468 = FStar_Syntax_Subst.compress t  in
                    uu____2468.FStar_Syntax_Syntax.n  in
                  (match uu____2467 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2527  ->
                                 match uu____2527 with
                                 | (x,imp) ->
                                     let uu____2546 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2546
                                     then
                                       let uu____2555 =
                                         let uu____2556 =
                                           let uu____2559 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2559
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2556
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2555, imp)
                                     else (x, imp)))
                          in
                       let uu____2566 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2566 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2587 =
                                let uu____2592 =
                                  let uu____2593 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2602 =
                                    let uu____2613 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2613]  in
                                  uu____2593 :: uu____2602  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2592
                                 in
                              uu____2587 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2648 = FStar_Util.prefix formals2  in
                            (match uu____2648 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___412_2711 = last1  in
                                   let uu____2712 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___412_2711.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___412_2711.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2712
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2748 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____2748
                                   then
                                     let uu____2751 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2753 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2755 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2751 uu____2753 uu____2755
                                   else ());
                                  (l, t', u_names))))
                   | uu____2762 ->
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
               let uu____2826 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2826)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3429 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3429
       then
         let uu____3432 =
           let uu____3434 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3434  in
         let uu____3436 = FStar_Syntax_Print.term_to_string e  in
         let uu____3438 =
           let uu____3440 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3440  in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3432
           uu____3436 uu____3438
       else ());
      (let uu____3444 =
         FStar_Util.record_time
           (fun uu____3463  ->
              tc_maybe_toplevel_term
                (let uu___431_3466 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___431_3466.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___431_3466.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___431_3466.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___431_3466.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___431_3466.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___431_3466.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___431_3466.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___431_3466.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___431_3466.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___431_3466.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___431_3466.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___431_3466.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___431_3466.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___431_3466.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___431_3466.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___431_3466.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___431_3466.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___431_3466.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___431_3466.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___431_3466.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___431_3466.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___431_3466.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___431_3466.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___431_3466.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___431_3466.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___431_3466.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___431_3466.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___431_3466.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___431_3466.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___431_3466.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___431_3466.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___431_3466.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___431_3466.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___431_3466.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___431_3466.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___431_3466.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___431_3466.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___431_3466.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___431_3466.FStar_TypeChecker_Env.nbe)
                 }) e)
          in
       match uu____3444 with
       | (r,ms) ->
           ((let uu____3491 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3491
             then
               ((let uu____3495 =
                   let uu____3497 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3497
                    in
                 let uu____3499 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3501 =
                   let uu____3503 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3503  in
                 let uu____3504 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3495 uu____3499 uu____3501 uu____3504);
                (let uu____3507 = r  in
                 match uu____3507 with
                 | (e1,uu____3515,uu____3516) ->
                     let uu____3517 =
                       let uu____3519 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3519
                        in
                     let uu____3521 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3523 =
                       let uu____3525 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3525  in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3517
                       uu____3521 uu____3523))
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
      (let uu____3543 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3543
       then
         let uu____3546 =
           let uu____3548 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3548  in
         let uu____3550 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3552 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3546 uu____3550
           uu____3552
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3563 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3593 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3600 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3613 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3614 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3615 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3616 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3617 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3636 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3651 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3658 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3674 =
             match uu___2_3674 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3680 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3696 =
                 let uu____3697 = FStar_Syntax_Subst.compress t  in
                 uu____3697.FStar_Syntax_Syntax.n  in
               match uu____3696 with
               | FStar_Syntax_Syntax.Tm_name uu____3701 -> true
               | uu____3703 -> false  in
             FStar_Util.for_some
               (fun uu____3713  ->
                  match uu____3713 with
                  | (uu____3719,t) ->
                      let uu____3721 = is_name1 t  in
                      Prims.op_Negation uu____3721)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3740  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3783  ->
                       match uu____3783 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___504_3812 = qi  in
                  let uu____3813 =
                    FStar_List.map
                      (fun uu____3841  ->
                         match uu____3841 with
                         | ((bv,uu____3857),bv') ->
                             let uu____3869 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____3869)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___504_3812.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3813
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
                         let uu____3881 =
                           let uu____3888 =
                             let uu____3889 =
                               let uu____3903 =
                                 let uu____3906 =
                                   let uu____3907 =
                                     let uu____3914 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____3914
                                      in
                                   [uu____3907]  in
                                 FStar_Syntax_Subst.close uu____3906 t  in
                               ((false, [lb]), uu____3903)  in
                             FStar_Syntax_Syntax.Tm_let uu____3889  in
                           FStar_Syntax_Syntax.mk uu____3888  in
                         uu____3881 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____3950 =
                  FStar_List.fold_right
                    (fun uu____3986  ->
                       fun uu____3987  ->
                         match (uu____3986, uu____3987) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4056 = tc_term env_tm tm  in
                             (match uu____4056 with
                              | (tm1,uu____4074,g) ->
                                  let uu____4076 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4076))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____3950 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___532_4118 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___532_4118.FStar_Syntax_Syntax.qkind);
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
                let uu____4137 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4137 with
                 | (env',uu____4151) ->
                     let uu____4156 =
                       tc_term
                         (let uu___541_4165 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___541_4165.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___541_4165.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___541_4165.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___541_4165.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___541_4165.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___541_4165.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___541_4165.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___541_4165.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___541_4165.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___541_4165.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___541_4165.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___541_4165.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___541_4165.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___541_4165.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___541_4165.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___541_4165.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___541_4165.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___541_4165.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___541_4165.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___541_4165.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___541_4165.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___541_4165.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___541_4165.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___541_4165.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___541_4165.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___541_4165.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___541_4165.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___541_4165.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___541_4165.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___541_4165.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___541_4165.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___541_4165.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___541_4165.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___541_4165.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___541_4165.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___541_4165.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___541_4165.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___541_4165.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___541_4165.FStar_TypeChecker_Env.nbe)
                          }) qt
                        in
                     (match uu____4156 with
                      | (qt1,uu____4174,uu____4175) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4181 =
                            let uu____4188 =
                              let uu____4193 =
                                FStar_Syntax_Util.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4193  in
                            value_check_expected_typ env1 top uu____4188
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4181 with
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
           { FStar_Syntax_Syntax.blob = uu____4210;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4211;
             FStar_Syntax_Syntax.ltyp = uu____4212;
             FStar_Syntax_Syntax.rng = uu____4213;_}
           ->
           let uu____4224 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4224
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4231 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4231 with
            | (e2,c,g) ->
                let g1 =
                  let uu___571_4248 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___571_4248.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___571_4248.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___571_4248.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____4249 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4249, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats,nopattern)) ->
           let uu____4294 = FStar_Syntax_Util.type_u ()  in
           (match uu____4294 with
            | (t,u) ->
                let uu____4307 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4307 with
                 | (e2,c,g) ->
                     let pats1 =
                       match pats with
                       | [] ->
                           let uu____4338 =
                             (FStar_Options.auto_patterns ()) &&
                               (Prims.op_Negation nopattern)
                              in
                           if uu____4338
                           then
                             let uu____4343 =
                               FStar_TypeChecker_PatternInference.infer_pattern
                                 env1 names1 e2
                                in
                             (match uu____4343 with
                              | [] ->
                                  ((let uu____4349 =
                                      let uu____4355 =
                                        let uu____4357 =
                                          FStar_Syntax_Print.term_to_string
                                            e2
                                           in
                                        let uu____4359 =
                                          let uu____4361 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Syntax_Print.tag_of_term
                                            uu____4361
                                           in
                                        let uu____4362 =
                                          let uu____4364 =
                                            FStar_All.pipe_right names1
                                              (FStar_List.map
                                                 FStar_Syntax_Print.term_to_string)
                                             in
                                          FStar_All.pipe_right uu____4364
                                            (FStar_String.concat ", ")
                                           in
                                        FStar_Util.format3
                                          "no pattern can be inferred : %s (%s) with names: (%s)\n"
                                          uu____4357 uu____4359 uu____4362
                                         in
                                      (FStar_Errors.Warning_NoPatternInferred,
                                        uu____4355)
                                       in
                                    FStar_Errors.log_issue
                                      e2.FStar_Syntax_Syntax.pos uu____4349);
                                   [])
                              | pats1 -> pats1)
                           else pats
                       | uu____4386 -> pats  in
                     let uu____4399 =
                       let uu____4416 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4416 with
                       | (env2,uu____4440) -> tc_smt_pats env2 pats1  in
                     (match uu____4399 with
                      | (pats2,g') ->
                          let g'1 =
                            let uu___602_4478 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___602_4478.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___602_4478.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___602_4478.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____4479 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats2, nopattern))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4499 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4479, c, uu____4499))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4505 =
             let uu____4506 = FStar_Syntax_Subst.compress e1  in
             uu____4506.FStar_Syntax_Syntax.n  in
           (match uu____4505 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4515,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4517;
                               FStar_Syntax_Syntax.lbtyp = uu____4518;
                               FStar_Syntax_Syntax.lbeff = uu____4519;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4521;
                               FStar_Syntax_Syntax.lbpos = uu____4522;_}::[]),e2)
                ->
                let uu____4553 =
                  let uu____4560 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4560 e11  in
                (match uu____4553 with
                 | (e12,c1,g1) ->
                     let uu____4570 = tc_term env1 e2  in
                     (match uu____4570 with
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
                            let uu____4594 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_Syntax_Syntax.eff_name
                               in
                            if uu____4594
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4604 =
                              let uu____4611 =
                                let uu____4612 =
                                  let uu____4626 =
                                    let uu____4634 =
                                      let uu____4637 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4637]  in
                                    (false, uu____4634)  in
                                  (uu____4626, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4612  in
                              FStar_Syntax_Syntax.mk uu____4611  in
                            uu____4604 FStar_Pervasives_Native.None
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
                          let uu____4661 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4661)))
            | uu____4662 ->
                let uu____4663 = tc_term env1 e1  in
                (match uu____4663 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4685) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4697) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4716 = tc_term env1 e1  in
           (match uu____4716 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4740) ->
           let uu____4787 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4787 with
            | (env0,uu____4801) ->
                let uu____4806 = tc_comp env0 expected_c  in
                (match uu____4806 with
                 | (expected_c1,uu____4820,g) ->
                     let uu____4822 =
                       let uu____4829 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4829 e1  in
                     (match uu____4822 with
                      | (e2,c',g') ->
                          let uu____4839 =
                            let uu____4846 =
                              let uu____4851 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____4851)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____4846
                             in
                          (match uu____4839 with
                           | (e3,expected_c2,g'') ->
                               let uu____4861 = tc_tactic_opt env0 topt  in
                               (match uu____4861 with
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
                                      let uu____4921 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____4921
                                       in
                                    let uu____4922 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____4922 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____4939 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____4939
                                            in
                                         let uu____4940 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____4940)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____4944) ->
           let uu____4991 = FStar_Syntax_Util.type_u ()  in
           (match uu____4991 with
            | (k,u) ->
                let uu____5004 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____5004 with
                 | (t1,uu____5018,f) ->
                     let uu____5020 = tc_tactic_opt env1 topt  in
                     (match uu____5020 with
                      | (topt1,gtac) ->
                          let uu____5039 =
                            let uu____5046 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5046 e1  in
                          (match uu____5039 with
                           | (e2,c,g) ->
                               let uu____5056 =
                                 let uu____5061 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5067  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5061 e2 c f
                                  in
                               (match uu____5056 with
                                | (c1,f1) ->
                                    let uu____5077 =
                                      let uu____5084 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5084
                                        c1
                                       in
                                    (match uu____5077 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5131 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5131
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5133 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5133)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5134;
              FStar_Syntax_Syntax.vars = uu____5135;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5214 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5214 with
            | (unary_op1,uu____5238) ->
                let head1 =
                  let uu____5266 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5266
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
              FStar_Syntax_Syntax.pos = uu____5314;
              FStar_Syntax_Syntax.vars = uu____5315;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5394 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5394 with
            | (unary_op1,uu____5418) ->
                let head1 =
                  let uu____5446 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5446
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
                (FStar_Const.Const_reflect uu____5494);
              FStar_Syntax_Syntax.pos = uu____5495;
              FStar_Syntax_Syntax.vars = uu____5496;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5575 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5575 with
            | (unary_op1,uu____5599) ->
                let head1 =
                  let uu____5627 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5627
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
              FStar_Syntax_Syntax.pos = uu____5675;
              FStar_Syntax_Syntax.vars = uu____5676;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5772 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5772 with
            | (unary_op1,uu____5796) ->
                let head1 =
                  let uu____5824 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5824
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
              FStar_Syntax_Syntax.pos = uu____5880;
              FStar_Syntax_Syntax.vars = uu____5881;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____5919 =
             let uu____5926 =
               let uu____5927 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5927  in
             tc_term uu____5926 e1  in
           (match uu____5919 with
            | (e2,c,g) ->
                let uu____5951 = FStar_Syntax_Util.head_and_args top  in
                (match uu____5951 with
                 | (head1,uu____5975) ->
                     let uu____6000 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6033 =
                       let uu____6034 =
                         let uu____6035 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6035  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____6034
                        in
                     (uu____6000, uu____6033, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6036;
              FStar_Syntax_Syntax.vars = uu____6037;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6090 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6090 with
            | (head1,uu____6114) ->
                let env' =
                  let uu____6140 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6140  in
                let uu____6141 = tc_term env' r  in
                (match uu____6141 with
                 | (er,uu____6155,gr) ->
                     let uu____6157 = tc_term env1 t  in
                     (match uu____6157 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6174 =
                            let uu____6175 =
                              let uu____6180 =
                                let uu____6181 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6190 =
                                  let uu____6201 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6201]  in
                                uu____6181 :: uu____6190  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6180
                               in
                            uu____6175 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6174, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6234;
              FStar_Syntax_Syntax.vars = uu____6235;_},uu____6236)
           ->
           let uu____6261 =
             let uu____6267 =
               let uu____6269 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6269  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6267)  in
           FStar_Errors.raise_error uu____6261 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6279;
              FStar_Syntax_Syntax.vars = uu____6280;_},uu____6281)
           ->
           let uu____6306 =
             let uu____6312 =
               let uu____6314 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6314  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6312)  in
           FStar_Errors.raise_error uu____6306 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6324;
              FStar_Syntax_Syntax.vars = uu____6325;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6372 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6372 with
             | (env0,uu____6386) ->
                 let uu____6391 = tc_term env0 e1  in
                 (match uu____6391 with
                  | (e2,c,g) ->
                      let uu____6407 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6407 with
                       | (reify_op,uu____6431) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_Syntax_Syntax.res_typ
                              in
                           let ef =
                             let uu____6458 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_Syntax_Util.comp_effect_name uu____6458
                              in
                           ((let uu____6462 =
                               let uu____6464 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef
                                  in
                               Prims.op_Negation uu____6464  in
                             if uu____6462
                             then
                               let uu____6467 =
                                 let uu____6473 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str
                                    in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____6473)
                                  in
                               FStar_Errors.raise_error uu____6467
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____6480 =
                                 FStar_Syntax_Syntax.lcomp_comp c  in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____6480 u_c
                                in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let c1 =
                               let uu____6517 =
                                 FStar_TypeChecker_Env.is_total_effect env1
                                   ef
                                  in
                               if uu____6517
                               then
                                 let uu____6520 =
                                   FStar_Syntax_Syntax.mk_Total repr  in
                                 FStar_All.pipe_right uu____6520
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
                                  let uu____6532 =
                                    FStar_Syntax_Syntax.mk_Comp ct  in
                                  FStar_All.pipe_right uu____6532
                                    FStar_Syntax_Util.lcomp_of_comp)
                                in
                             let uu____6533 =
                               comp_check_expected_typ env1 e3 c1  in
                             match uu____6533 with
                             | (e4,c2,g') ->
                                 let uu____6549 =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 (e4, c2, uu____6549)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6551;
              FStar_Syntax_Syntax.vars = uu____6552;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6600 =
               let uu____6602 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6602  in
             if uu____6600
             then
               let uu____6605 =
                 let uu____6611 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6611)  in
               FStar_Errors.raise_error uu____6605 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6617 = FStar_Syntax_Util.head_and_args top  in
             match uu____6617 with
             | (reflect_op,uu____6641) ->
                 let uu____6666 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6666 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6706 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6706 with
                       | (env_no_ex,topt) ->
                           let uu____6725 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____6745 =
                                 let uu____6752 =
                                   let uu____6753 =
                                     let uu____6770 =
                                       let uu____6781 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6790 =
                                         let uu____6801 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6801]  in
                                       uu____6781 :: uu____6790  in
                                     (repr, uu____6770)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6753  in
                                 FStar_Syntax_Syntax.mk uu____6752  in
                               uu____6745 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6846 =
                               let uu____6853 =
                                 let uu____6854 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6854
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6853 t  in
                             match uu____6846 with
                             | (t1,uu____6880,g) ->
                                 let uu____6882 =
                                   let uu____6883 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____6883.FStar_Syntax_Syntax.n  in
                                 (match uu____6882 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____6896,(res,uu____6898)::(wp,uu____6900)::[])
                                      -> (t1, res, wp, g)
                                  | uu____6957 -> failwith "Impossible")
                              in
                           (match uu____6725 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____6983 =
                                  let uu____6990 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____6990 with
                                  | (e2,c,g) ->
                                      ((let uu____7007 =
                                          let uu____7009 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____7009
                                           in
                                        if uu____7007
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7032 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7032 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7043 =
                                                let uu____7053 =
                                                  let uu____7061 =
                                                    let uu____7063 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7065 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7063 uu____7065
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7061,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7053]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7043);
                                             (let uu____7083 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7083)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7087 =
                                              let uu____7088 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7088
                                               in
                                            (e2, uu____7087)))
                                   in
                                (match uu____6983 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7104 =
                                         let uu____7105 =
                                           let uu____7106 =
                                             let uu____7107 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7107]  in
                                           let uu____7108 =
                                             let uu____7119 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7119]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7106;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7108;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7105
                                          in
                                       FStar_All.pipe_right uu____7104
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7179 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7179 with
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
                                          let uu____7202 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7202))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7241 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7241 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7291,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7292))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7345 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7345 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7420 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7630 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7420 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7749 =
               let uu____7750 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7750 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7749 instantiate_both  in
           ((let uu____7766 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7766
             then
               let uu____7769 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7771 = FStar_Syntax_Print.term_to_string top  in
               let uu____7773 =
                 let uu____7775 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7775
                   (fun uu___3_7782  ->
                      match uu___3_7782 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7769
                 uu____7771 uu____7773
             else ());
            (let uu____7791 = tc_term (no_inst env2) head1  in
             match uu____7791 with
             | (head2,chead,g_head) ->
                 let uu____7807 =
                   let uu____7814 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____7817 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____7817))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____7814
                   then
                     let uu____7826 =
                       let uu____7833 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____7833
                        in
                     match uu____7826 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____7847 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____7847)
                    in
                 (match uu____7807 with
                  | (e1,c,g) ->
                      let uu____7859 =
                        let uu____7866 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____7866
                        then
                          let uu____7875 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____7875 with
                          | (e2,res_typ,implicits) ->
                              let uu____7891 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____7891, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____7859 with
                       | (e2,c1,implicits) ->
                           ((let uu____7904 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____7904
                             then
                               let uu____7907 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____7907
                             else ());
                            (let uu____7912 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____7912 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____7931 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____7931
                                   then
                                     let uu____7934 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____7936 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____7934 uu____7936
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____7979 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____7979 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____7999 = tc_term env12 e1  in
                (match uu____7999 with
                 | (e11,c1,g1) ->
                     let uu____8015 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8029 = FStar_Syntax_Util.type_u ()  in
                           (match uu____8029 with
                            | (k,uu____8041) ->
                                let uu____8042 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8042 with
                                 | (res_t,uu____8063,g) ->
                                     let uu____8077 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8078 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8077, res_t, uu____8078)))
                        in
                     (match uu____8015 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8089 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8089
                            then
                              let uu____8092 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8092
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
                            let uu____8219 =
                              let uu____8224 =
                                FStar_List.fold_right
                                  (fun uu____8306  ->
                                     fun uu____8307  ->
                                       match (uu____8306, uu____8307) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____8552 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8552)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____8224 with
                              | (cases,g) ->
                                  let uu____8657 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8657, g)
                               in
                            match uu____8219 with
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
                                           (fun uu____8799  ->
                                              match uu____8799 with
                                              | ((pat,wopt,br),uu____8844,eff_label,uu____8846,uu____8847,uu____8848)
                                                  ->
                                                  let uu____8885 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____8885)))
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
                                  let uu____8952 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____8952
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____8960 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____8960  in
                                     let lb =
                                       let uu____8964 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____8964 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____8970 =
                                         let uu____8977 =
                                           let uu____8978 =
                                             let uu____8992 =
                                               let uu____8995 =
                                                 let uu____8996 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____8996]  in
                                               FStar_Syntax_Subst.close
                                                 uu____8995 e_match
                                                in
                                             ((false, [lb]), uu____8992)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____8978
                                            in
                                         FStar_Syntax_Syntax.mk uu____8977
                                          in
                                       uu____8970
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____9029 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____9029
                                  then
                                    let uu____9032 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9034 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____9032 uu____9034
                                  else ());
                                 (let uu____9039 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____9039))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9040;
                FStar_Syntax_Syntax.lbunivs = uu____9041;
                FStar_Syntax_Syntax.lbtyp = uu____9042;
                FStar_Syntax_Syntax.lbeff = uu____9043;
                FStar_Syntax_Syntax.lbdef = uu____9044;
                FStar_Syntax_Syntax.lbattrs = uu____9045;
                FStar_Syntax_Syntax.lbpos = uu____9046;_}::[]),uu____9047)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9073),uu____9074) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9092;
                FStar_Syntax_Syntax.lbunivs = uu____9093;
                FStar_Syntax_Syntax.lbtyp = uu____9094;
                FStar_Syntax_Syntax.lbeff = uu____9095;
                FStar_Syntax_Syntax.lbdef = uu____9096;
                FStar_Syntax_Syntax.lbattrs = uu____9097;
                FStar_Syntax_Syntax.lbpos = uu____9098;_}::uu____9099),uu____9100)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9128),uu____9129) ->
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
          let uu____9163 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9202))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9243 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9163 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9276 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9276 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9280 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9280)
                 in
              let uu____9283 =
                let uu____9290 =
                  let uu____9291 =
                    let uu____9292 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9292
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9291  in
                tc_term uu____9290 typ  in
              (match uu____9283 with
               | (typ1,uu____9308,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9311 = tc_tactic env tau  in
                     match uu____9311 with
                     | (tau1,uu____9325,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1199_9330 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1199_9330.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1199_9330.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9332 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9332
                            then
                              let uu____9337 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9337
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9343 =
                              let uu____9344 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_Syntax_Util.lcomp_of_comp uu____9344
                               in
                            (t, uu____9343,
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
        let uu___1207_9348 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1207_9348.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1207_9348.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1207_9348.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1207_9348.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1207_9348.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1207_9348.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1207_9348.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1207_9348.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1207_9348.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1207_9348.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1207_9348.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1207_9348.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1207_9348.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1207_9348.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1207_9348.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1207_9348.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1207_9348.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1207_9348.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1207_9348.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1207_9348.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1207_9348.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1207_9348.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1207_9348.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1207_9348.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1207_9348.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1207_9348.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1207_9348.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1207_9348.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1207_9348.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1207_9348.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1207_9348.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1207_9348.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1207_9348.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1207_9348.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1207_9348.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1207_9348.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1207_9348.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1207_9348.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1207_9348.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1207_9348.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1207_9348.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1207_9348.FStar_TypeChecker_Env.nbe)
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
          let uu____9371 = tc_tactic env tactic  in
          (match uu____9371 with
           | (tactic1,uu____9385,g) ->
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
        let uu____9437 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9437 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9458 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9458
              then FStar_Util.Inl t
              else
                (let uu____9467 =
                   let uu____9468 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____9468
                    in
                 FStar_Util.Inr uu____9467)
               in
            let is_data_ctor uu___4_9477 =
              match uu___4_9477 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9482) -> true
              | uu____9490 -> false  in
            let uu____9494 =
              (is_data_ctor dc) &&
                (let uu____9497 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9497)
               in
            if uu____9494
            then
              let uu____9506 =
                let uu____9512 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9512)  in
              let uu____9516 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9506 uu____9516
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9534 =
            let uu____9536 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9536
             in
          failwith uu____9534
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9563 =
            let uu____9568 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9568  in
          value_check_expected_typ env1 e uu____9563
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9570 =
            let uu____9583 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9583 with
            | FStar_Pervasives_Native.None  ->
                let uu____9598 = FStar_Syntax_Util.type_u ()  in
                (match uu____9598 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9570 with
           | (t,uu____9636,g0) ->
               let uu____9650 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____9650 with
                | (e1,uu____9671,g1) ->
                    let uu____9685 =
                      let uu____9686 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9686
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____9687 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9685, uu____9687)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9689 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9699 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9699)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9689 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1272_9713 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1272_9713.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1272_9713.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9716 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9716 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9737 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9737
                       then FStar_Util.Inl t1
                       else
                         (let uu____9746 =
                            let uu____9747 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____9747
                             in
                          FStar_Util.Inr uu____9746)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9749;
             FStar_Syntax_Syntax.vars = uu____9750;_},uu____9751)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9756 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9756
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9766 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9766
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9776;
             FStar_Syntax_Syntax.vars = uu____9777;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____9786 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9786 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9810 =
                     let uu____9816 =
                       let uu____9818 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____9820 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____9822 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9818 uu____9820 uu____9822
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9816)
                      in
                   let uu____9826 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____9810 uu____9826)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9843 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9848 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9848 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9850 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9850 with
           | ((us,t),range) ->
               ((let uu____9873 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____9873
                 then
                   let uu____9878 =
                     let uu____9880 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____9880  in
                   let uu____9881 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____9883 = FStar_Range.string_of_range range  in
                   let uu____9885 = FStar_Range.string_of_use_range range  in
                   let uu____9887 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____9878 uu____9881 uu____9883 uu____9885 uu____9887
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9895 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9895 us  in
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
          let uu____9923 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9923 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____9937 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9937 with
                | (env2,uu____9951) ->
                    let uu____9956 = tc_binders env2 bs1  in
                    (match uu____9956 with
                     | (bs2,env3,g,us) ->
                         let uu____9975 = tc_comp env3 c1  in
                         (match uu____9975 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1352_9994 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1352_9994.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1352_9994.FStar_Syntax_Syntax.vars)
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
                                  let uu____10005 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10005
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
          let uu____10021 =
            let uu____10026 =
              let uu____10027 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10027]  in
            FStar_Syntax_Subst.open_term uu____10026 phi  in
          (match uu____10021 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10055 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10055 with
                | (env2,uu____10069) ->
                    let uu____10074 =
                      let uu____10089 = FStar_List.hd x1  in
                      tc_binder env2 uu____10089  in
                    (match uu____10074 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10125 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10125
                           then
                             let uu____10128 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10130 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10132 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10128 uu____10130 uu____10132
                           else ());
                          (let uu____10139 = FStar_Syntax_Util.type_u ()  in
                           match uu____10139 with
                           | (t_phi,uu____10151) ->
                               let uu____10152 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10152 with
                                | (phi2,uu____10166,f2) ->
                                    let e1 =
                                      let uu___1390_10171 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1390_10171.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1390_10171.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10180 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10180
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10208) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10235 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10235
            then
              let uu____10238 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1403_10242 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1403_10242.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1403_10242.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10238
            else ());
           (let uu____10258 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10258 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10271 ->
          let uu____10272 =
            let uu____10274 = FStar_Syntax_Print.term_to_string top  in
            let uu____10276 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10274
              uu____10276
             in
          failwith uu____10272

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10288 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10290,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10303,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____10321 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10327 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10329 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10330 ->
            let uu____10332 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10332 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10337 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10338 =
              let uu____10344 =
                let uu____10346 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10346
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10344)  in
            FStar_Errors.raise_error uu____10338 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10350 =
              let uu____10356 =
                let uu____10358 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10358
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10356)  in
            FStar_Errors.raise_error uu____10350 r
        | FStar_Const.Const_reify  ->
            let uu____10362 =
              let uu____10368 =
                let uu____10370 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10370
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10368)  in
            FStar_Errors.raise_error uu____10362 r
        | FStar_Const.Const_reflect uu____10374 ->
            let uu____10375 =
              let uu____10381 =
                let uu____10383 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10383
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10381)  in
            FStar_Errors.raise_error uu____10375 r
        | uu____10387 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____10406) ->
          let uu____10415 = FStar_Syntax_Util.type_u ()  in
          (match uu____10415 with
           | (k,u) ->
               let uu____10428 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10428 with
                | (t1,uu____10442,g) ->
                    let uu____10444 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10444, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10446) ->
          let uu____10455 = FStar_Syntax_Util.type_u ()  in
          (match uu____10455 with
           | (k,u) ->
               let uu____10468 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10468 with
                | (t1,uu____10482,g) ->
                    let uu____10484 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10484, u, g)))
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
            let uu____10494 =
              let uu____10499 =
                let uu____10500 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10500 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10499  in
            uu____10494 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10517 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10517 with
           | (tc1,uu____10531,f) ->
               let uu____10533 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10533 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10583 =
                        let uu____10584 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10584.FStar_Syntax_Syntax.n  in
                      match uu____10583 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10587,us) -> us
                      | uu____10593 -> []  in
                    let uu____10594 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10594 with
                     | (uu____10617,args1) ->
                         let uu____10643 =
                           let uu____10666 = FStar_List.hd args1  in
                           let uu____10683 = FStar_List.tl args1  in
                           (uu____10666, uu____10683)  in
                         (match uu____10643 with
                          | (res,args2) ->
                              let uu____10764 =
                                let uu____10773 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10801  ->
                                          match uu___5_10801 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10809 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____10809 with
                                               | (env1,uu____10821) ->
                                                   let uu____10826 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____10826 with
                                                    | (e1,uu____10838,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____10773
                                  FStar_List.unzip
                                 in
                              (match uu____10764 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1532_10879 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1532_10879.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1532_10879.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____10885 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____10885))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____10895 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____10899 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____10909 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____10909
        | FStar_Syntax_Syntax.U_max us ->
            let uu____10913 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____10913
        | FStar_Syntax_Syntax.U_name x ->
            let uu____10917 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____10917
            then u2
            else
              (let uu____10922 =
                 let uu____10924 =
                   let uu____10926 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____10926 " not found"  in
                 Prims.op_Hat "Universe variable " uu____10924  in
               failwith uu____10922)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____10933 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____10933 FStar_Pervasives_Native.snd
         | uu____10942 -> aux u)

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
            let uu____10973 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____10973 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11062 bs2 bs_expected1 =
              match uu____11062 with
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
                              uu____11253),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11254)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11269),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11270)) -> true
                           | uu____11279 -> false  in
                         let uu____11289 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11292 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11292 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11289
                         then
                           let uu____11294 =
                             let uu____11300 =
                               let uu____11302 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11302
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11300)
                              in
                           let uu____11306 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11294 uu____11306
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11310 =
                           let uu____11317 =
                             let uu____11318 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11318.FStar_Syntax_Syntax.n  in
                           match uu____11317 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11329 ->
                               ((let uu____11331 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11331
                                 then
                                   let uu____11334 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11334
                                 else ());
                                (let uu____11339 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11339 with
                                 | (t,uu____11353,g1_env) ->
                                     let g2_env =
                                       let uu____11356 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11356
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11361 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11361 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11364 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11370 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11364 uu____11370
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____11372 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____11372
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11374 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11374)))
                            in
                         match uu____11310 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1630_11400 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1630_11400.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1630_11400.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11423 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11423
                                in
                             let uu____11426 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11426 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11491 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11491,
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
                  | uu____11663 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11673 = tc_binders env1 bs  in
                  match uu____11673 with
                  | (bs1,envbody,g_env,uu____11703) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____11759 =
                    let uu____11760 = FStar_Syntax_Subst.compress t2  in
                    uu____11760.FStar_Syntax_Syntax.n  in
                  match uu____11759 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11793 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11813 -> failwith "Impossible");
                       (let uu____11823 = tc_binders env1 bs  in
                        match uu____11823 with
                        | (bs1,envbody,g_env,uu____11865) ->
                            let uu____11866 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____11866 with
                             | (envbody1,uu____11904) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____11925;
                         FStar_Syntax_Syntax.pos = uu____11926;
                         FStar_Syntax_Syntax.vars = uu____11927;_},uu____11928)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11972 -> failwith "Impossible");
                       (let uu____11982 = tc_binders env1 bs  in
                        match uu____11982 with
                        | (bs1,envbody,g_env,uu____12024) ->
                            let uu____12025 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12025 with
                             | (envbody1,uu____12063) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12085) ->
                      let uu____12090 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12090 with
                       | (uu____12151,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12228 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12228 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12373 c_expected2
                               body3 =
                               match uu____12373 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12487 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12487,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12504 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12504
                                           in
                                        let uu____12505 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12505,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12522 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12522
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
                                               let uu____12588 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12588 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12615 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12615 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12670 =
                                                           let uu____12697 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12697,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12670
                                                           c_expected4 body3))
                                           | uu____12720 ->
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
                             let uu____12749 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____12749 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1756_12814 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1756_12814.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1756_12814.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1756_12814.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1756_12814.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1756_12814.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1756_12814.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1756_12814.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1756_12814.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1756_12814.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1756_12814.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1756_12814.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1756_12814.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1756_12814.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1756_12814.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1756_12814.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1756_12814.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1756_12814.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1756_12814.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1756_12814.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1756_12814.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1756_12814.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1756_12814.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1756_12814.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1756_12814.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1756_12814.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1756_12814.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1756_12814.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1756_12814.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1756_12814.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1756_12814.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1756_12814.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1756_12814.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1756_12814.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1756_12814.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1756_12814.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1756_12814.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1756_12814.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1756_12814.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1756_12814.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1756_12814.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1756_12814.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1756_12814.FStar_TypeChecker_Env.nbe)
                               }  in
                             let uu____12821 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____12887  ->
                                       fun uu____12888  ->
                                         match (uu____12887, uu____12888)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____12979 =
                                               let uu____12986 =
                                                 let uu____12987 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____12987
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____12986 t3  in
                                             (match uu____12979 with
                                              | (t4,uu____13011,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____13024 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1774_13027
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1774_13027.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1774_13027.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____13024 ::
                                                          letrec_binders
                                                    | uu____13028 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13033 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13033)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____12821 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13053 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13053)
                              in
                           let uu____13056 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13056 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13132 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13132 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13179 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13179))))
                  | uu____13196 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13228 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____13228
                      else
                        (let uu____13232 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13232 with
                         | (uu____13281,bs1,uu____13283,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13315 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13315 with
          | (env1,topt) ->
              ((let uu____13335 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13335
                then
                  let uu____13338 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13338
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13352 = expected_function_typ1 env1 topt body  in
                match uu____13352 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13393 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13393
                      then
                        let uu____13398 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13401 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13398 uu____13401
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13407 =
                        let should_check_expected_effect =
                          let uu____13420 =
                            let uu____13427 =
                              let uu____13428 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13428.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13427)  in
                          match uu____13420 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13434,(FStar_Util.Inr
                                           expected_c,uu____13436),uu____13437))
                              -> false
                          | uu____13487 -> true  in
                        let uu____13495 =
                          tc_term
                            (let uu___1836_13504 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1836_13504.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1836_13504.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1836_13504.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1836_13504.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1836_13504.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1836_13504.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1836_13504.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1836_13504.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1836_13504.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1836_13504.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1836_13504.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1836_13504.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1836_13504.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1836_13504.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1836_13504.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1836_13504.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1836_13504.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1836_13504.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1836_13504.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1836_13504.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1836_13504.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1836_13504.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1836_13504.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1836_13504.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1836_13504.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1836_13504.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1836_13504.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1836_13504.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1836_13504.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1836_13504.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1836_13504.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1836_13504.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1836_13504.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1836_13504.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1836_13504.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1836_13504.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1836_13504.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1836_13504.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1836_13504.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1836_13504.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1836_13504.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____13495 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13531 =
                                let uu____13538 =
                                  let uu____13543 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____13543)  in
                                check_expected_effect
                                  (let uu___1844_13546 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___1844_13546.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___1844_13546.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___1844_13546.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___1844_13546.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___1844_13546.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___1844_13546.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___1844_13546.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___1844_13546.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___1844_13546.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___1844_13546.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___1844_13546.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___1844_13546.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___1844_13546.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___1844_13546.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___1844_13546.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___1844_13546.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___1844_13546.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___1844_13546.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___1844_13546.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___1844_13546.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___1844_13546.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___1844_13546.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___1844_13546.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___1844_13546.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___1844_13546.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___1844_13546.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___1844_13546.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___1844_13546.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___1844_13546.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___1844_13546.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___1844_13546.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___1844_13546.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___1844_13546.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___1844_13546.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___1844_13546.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___1844_13546.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___1844_13546.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___1844_13546.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___1844_13546.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___1844_13546.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___1844_13546.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___1844_13546.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____13538
                                 in
                              (match uu____13531 with
                               | (body3,cbody1,guard) ->
                                   let uu____13560 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____13560))
                            else
                              (let uu____13567 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____13567, guard_body1))
                         in
                      match uu____13407 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13592 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13595 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13595)
                               in
                            if uu____13592
                            then
                              let uu____13598 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13599 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13598
                                uu____13599
                            else
                              (let guard =
                                 let uu____13603 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13603
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
                          let uu____13617 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13638
                                     -> (e, t1, guard1)
                                 | uu____13653 ->
                                     let uu____13654 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13654 with
                                      | (e1,guard') ->
                                          let uu____13667 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____13667)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13617 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13678 =
                                 let uu____13683 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13683 guard2
                                  in
                               (match uu____13678 with
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
              (let uu____13732 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____13732
               then
                 let uu____13735 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____13737 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13735
                   uu____13737
               else ());
              (let monadic_application uu____13815 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____13815 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____13876 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____13876 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___1904_13890 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___1904_13890.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___1904_13890.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___1904_13890.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____13891 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____13907 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____13907
                                   in
                                (cres1, g)
                            | uu____13908 ->
                                let g =
                                  let uu____13918 =
                                    let uu____13919 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____13919
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____13918
                                   in
                                let uu____13920 =
                                  let uu____13921 =
                                    let uu____13922 =
                                      let uu____13923 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____13923
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____13922
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____13921
                                   in
                                (uu____13920, g)
                             in
                          (match uu____13891 with
                           | (cres2,guard1) ->
                               ((let uu____13935 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____13935
                                 then
                                   let uu____13938 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____13938
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____13958  ->
                                             match uu____13958 with
                                             | (uu____13968,uu____13969,lc)
                                                 ->
                                                 (let uu____13977 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____13977)
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
                                   let uu____13990 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____13990
                                   then
                                     ((let uu____13994 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13994
                                       then
                                         let uu____13997 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____13997
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____14005 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____14005
                                       then
                                         let uu____14008 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____14008
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____14039  ->
                                          match uu____14039 with
                                          | ((e,q),x,c) ->
                                              ((let uu____14081 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14081
                                                then
                                                  let uu____14084 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____14089 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14091 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____14084 uu____14089
                                                    uu____14091
                                                else ());
                                               (let uu____14096 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14096
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
                                   (let uu____14107 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____14107
                                    then
                                      let uu____14110 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____14110
                                    else ());
                                   (let uu____14115 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____14115
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
                                   let uu____14127 =
                                     let uu____14128 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____14128.FStar_Syntax_Syntax.n  in
                                   match uu____14127 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____14133 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____14156  ->
                                              match uu____14156 with
                                              | (arg,uu____14170,uu____14171)
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
                                     (let uu____14182 =
                                        let map_fun uu____14248 =
                                          match uu____14248 with
                                          | ((e,q),uu____14289,c) ->
                                              ((let uu____14312 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14312
                                                then
                                                  let uu____14315 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14317 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____14315 uu____14317
                                                else ());
                                               (let uu____14322 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14322
                                                then
                                                  ((let uu____14348 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14348
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
                                                       (let uu____14389 =
                                                          let uu____14391 =
                                                            let uu____14392 =
                                                              FStar_Syntax_Util.un_uinst
                                                                head2
                                                               in
                                                            uu____14392.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____14391
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let uu____14397
                                                                =
                                                                FStar_Parser_Const.psconst
                                                                  "ignore"
                                                                 in
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv
                                                                uu____14397
                                                          | uu____14399 ->
                                                              true
                                                           in
                                                        Prims.op_Negation
                                                          uu____14389)
                                                      in
                                                   if warn_effectful_args
                                                   then
                                                     (let uu____14403 =
                                                        let uu____14409 =
                                                          let uu____14411 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e
                                                             in
                                                          let uu____14413 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head2
                                                             in
                                                          FStar_Util.format3
                                                            "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                            uu____14411
                                                            (c.FStar_Syntax_Syntax.eff_name).FStar_Ident.str
                                                            uu____14413
                                                           in
                                                        (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                          uu____14409)
                                                         in
                                                      FStar_Errors.log_issue
                                                        e.FStar_Syntax_Syntax.pos
                                                        uu____14403)
                                                   else ();
                                                   (let uu____14420 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14420
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
                                                    let uu____14428 =
                                                      let uu____14437 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____14437, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____14428)))))
                                           in
                                        let uu____14466 =
                                          let uu____14497 =
                                            let uu____14526 =
                                              let uu____14537 =
                                                let uu____14546 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____14546,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____14537 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____14526
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____14497
                                           in
                                        match uu____14466 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____14747 =
                                              let uu____14748 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____14748
                                               in
                                            let uu____14769 =
                                              let uu____14770 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____14770  in
                                            (lifted_args, uu____14747,
                                              uu____14769)
                                         in
                                      match uu____14182 with
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
                                          let bind_lifted_args e uu___6_14881
                                            =
                                            match uu___6_14881 with
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
                                                  let uu____14942 =
                                                    let uu____14949 =
                                                      let uu____14950 =
                                                        let uu____14964 =
                                                          let uu____14967 =
                                                            let uu____14968 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____14968]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____14967 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____14964)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____14950
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____14949
                                                     in
                                                  uu____14942
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
                                 let uu____15020 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____15020 with
                                 | (comp3,g) ->
                                     ((let uu____15038 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____15038
                                       then
                                         let uu____15041 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____15043 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____15041 uu____15043
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____15124 bs args1 =
                 match uu____15124 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15263))::rest,
                         (uu____15265,FStar_Pervasives_Native.None )::uu____15266)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15327 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15327 with
                           | (t1,g_ex) ->
                               let uu____15340 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15340 with
                                | (varg,uu____15361,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15389 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15389)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15398 =
                                      let uu____15433 =
                                        let uu____15444 =
                                          let uu____15453 =
                                            let uu____15454 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15454
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15453)
                                           in
                                        uu____15444 :: outargs  in
                                      (subst2, uu____15433, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15398 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15500,FStar_Pervasives_Native.None
                                                                 )::uu____15501)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15563 = tc_tactic env tau1  in
                          (match uu____15563 with
                           | (tau2,uu____15577,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15580 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15580 with
                                | (t1,g_ex) ->
                                    let uu____15593 =
                                      let uu____15606 =
                                        let uu____15613 =
                                          let uu____15618 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15618, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15613
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15606
                                       in
                                    (match uu____15593 with
                                     | (varg,uu____15631,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15659 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15659)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____15668 =
                                           let uu____15703 =
                                             let uu____15714 =
                                               let uu____15723 =
                                                 let uu____15724 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____15724
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15723)
                                                in
                                             uu____15714 :: outargs  in
                                           (subst2, uu____15703, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____15668 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____15840,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15841)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____15852),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15853)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____15861),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15862)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____15877 ->
                                let uu____15886 =
                                  let uu____15892 =
                                    let uu____15894 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____15896 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____15898 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____15900 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____15894 uu____15896 uu____15898
                                      uu____15900
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____15892)
                                   in
                                FStar_Errors.raise_error uu____15886
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2114_15907 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2114_15907.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2114_15907.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____15909 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____15909
                             then
                               let uu____15912 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____15914 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15916 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15918 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____15920 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____15912 uu____15914 uu____15916
                                 uu____15918 uu____15920
                             else ());
                            (let uu____15925 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____15925 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2123_15940 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2123_15940.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2123_15940.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2123_15940.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2123_15940.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2123_15940.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2123_15940.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2123_15940.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2123_15940.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2123_15940.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2123_15940.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2123_15940.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2123_15940.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2123_15940.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2123_15940.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2123_15940.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2123_15940.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2123_15940.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2123_15940.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2123_15940.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2123_15940.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2123_15940.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2123_15940.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2123_15940.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2123_15940.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2123_15940.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2123_15940.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2123_15940.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2123_15940.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2123_15940.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2123_15940.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2123_15940.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2123_15940.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2123_15940.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2123_15940.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2123_15940.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2123_15940.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2123_15940.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2123_15940.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2123_15940.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2123_15940.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2123_15940.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2123_15940.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____15942 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____15942
                                   then
                                     let uu____15945 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____15947 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____15949 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____15945 uu____15947 uu____15949
                                   else ());
                                  (let uu____15954 = tc_term env2 e  in
                                   match uu____15954 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____15971 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____15971
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____15994 =
                                           let uu____15997 =
                                             let uu____16006 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16006
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____15997
                                            in
                                         (uu____15994, aq)  in
                                       let uu____16015 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____16015
                                       then
                                         let subst2 =
                                           let uu____16025 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16025 e1
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
                      | (uu____16124,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16160) ->
                          let uu____16211 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16211 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____16267 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____16267
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____16298 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____16298 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____16320 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____16320)
                                             in
                                          ((let uu____16322 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____16322
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
                                 | uu____16369 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____16377 =
                                         let uu____16378 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____16378.FStar_Syntax_Syntax.n
                                          in
                                       match uu____16377 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____16381;
                                              FStar_Syntax_Syntax.index =
                                                uu____16382;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____16384)
                                           -> norm_tres tres4
                                       | uu____16392 -> tres3  in
                                     let uu____16393 = norm_tres tres1  in
                                     aux true solve ghead2 uu____16393
                                 | uu____16395 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____16398 ->
                                     let uu____16399 =
                                       let uu____16405 =
                                         let uu____16407 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____16409 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____16411 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____16407 uu____16409
                                           uu____16411
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____16405)
                                        in
                                     let uu____16415 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____16399
                                       uu____16415
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____16445 =
                   let uu____16446 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16446.FStar_Syntax_Syntax.n  in
                 match uu____16445 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16455 ->
                     let uu____16468 =
                       FStar_List.fold_right
                         (fun uu____16499  ->
                            fun uu____16500  ->
                              match uu____16500 with
                              | (bs,guard1) ->
                                  let uu____16527 =
                                    let uu____16540 =
                                      let uu____16541 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16541
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16540
                                     in
                                  (match uu____16527 with
                                   | (t,uu____16558,g) ->
                                       let uu____16572 =
                                         let uu____16575 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16575 :: bs  in
                                       let uu____16576 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16572, uu____16576))) args
                         ([], guard)
                        in
                     (match uu____16468 with
                      | (bs,guard1) ->
                          let uu____16593 =
                            let uu____16600 =
                              let uu____16613 =
                                let uu____16614 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16614
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16613
                               in
                            match uu____16600 with
                            | (t,uu____16631,g) ->
                                let uu____16645 = FStar_Options.ml_ish ()  in
                                if uu____16645
                                then
                                  let uu____16654 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16657 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16654, uu____16657)
                                else
                                  (let uu____16662 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16665 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16662, uu____16665))
                             in
                          (match uu____16593 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16684 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16684
                                 then
                                   let uu____16688 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16690 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16692 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16688 uu____16690 uu____16692
                                 else ());
                                (let g =
                                   let uu____16698 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16698
                                    in
                                 let uu____16699 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16699))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16700;
                        FStar_Syntax_Syntax.pos = uu____16701;
                        FStar_Syntax_Syntax.vars = uu____16702;_},uu____16703)
                     ->
                     let uu____16740 =
                       FStar_List.fold_right
                         (fun uu____16771  ->
                            fun uu____16772  ->
                              match uu____16772 with
                              | (bs,guard1) ->
                                  let uu____16799 =
                                    let uu____16812 =
                                      let uu____16813 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16813
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16812
                                     in
                                  (match uu____16799 with
                                   | (t,uu____16830,g) ->
                                       let uu____16844 =
                                         let uu____16847 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16847 :: bs  in
                                       let uu____16848 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16844, uu____16848))) args
                         ([], guard)
                        in
                     (match uu____16740 with
                      | (bs,guard1) ->
                          let uu____16865 =
                            let uu____16872 =
                              let uu____16885 =
                                let uu____16886 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16886
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16885
                               in
                            match uu____16872 with
                            | (t,uu____16903,g) ->
                                let uu____16917 = FStar_Options.ml_ish ()  in
                                if uu____16917
                                then
                                  let uu____16926 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16929 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16926, uu____16929)
                                else
                                  (let uu____16934 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16937 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16934, uu____16937))
                             in
                          (match uu____16865 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16956 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16956
                                 then
                                   let uu____16960 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16962 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16964 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16960 uu____16962 uu____16964
                                 else ());
                                (let g =
                                   let uu____16970 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16970
                                    in
                                 let uu____16971 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16971))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____16994 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____16994 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____17016 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____17016)  in
                          ((let uu____17018 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17018
                            then
                              let uu____17021 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17023 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17025 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17028 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17021 uu____17023 uu____17025
                                uu____17028
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17074) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17080,uu____17081) ->
                     check_function_app t guard
                 | uu____17122 ->
                     let uu____17123 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17123
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
                  let uu____17206 =
                    FStar_List.fold_left2
                      (fun uu____17275  ->
                         fun uu____17276  ->
                           fun uu____17277  ->
                             match (uu____17275, uu____17276, uu____17277)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17430 =
                                     let uu____17432 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17432 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17430
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17438 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17438 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17467 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17467 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17472 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17472)
                                              &&
                                              (let uu____17475 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____17475))
                                          in
                                       let uu____17477 =
                                         let uu____17488 =
                                           let uu____17499 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17499]  in
                                         FStar_List.append seen uu____17488
                                          in
                                       let uu____17532 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17477, uu____17532, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17206 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17600 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17600
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____17603 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17603 with | (c2,g) -> (e, c2, g)))
              | uu____17620 ->
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
            let uu____17711 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17711 with
            | (head1,args) ->
                let uu____17754 =
                  let uu____17755 = FStar_Syntax_Subst.compress head1  in
                  uu____17755.FStar_Syntax_Syntax.n  in
                (match uu____17754 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____17759;
                        FStar_Syntax_Syntax.vars = uu____17760;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____17767 ->
                     if norm1
                     then t1
                     else
                       (let uu____17771 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____17771))
          
          and unfold_once t f us args =
            let uu____17789 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____17789
            then t
            else
              (let uu____17794 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____17794 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____17814 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____17814 with
                    | (uu____17819,head_def) ->
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
          let uu____17826 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____17826  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____17845 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____17845
           then
             let uu____17850 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____17852 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____17850 uu____17852
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____17872 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____17874 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____17872 uu____17874 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____17878 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____17878 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____17922 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____17922 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____17923;
                    FStar_Syntax_Syntax.pos = uu____17924;
                    FStar_Syntax_Syntax.vars = uu____17925;_} ->
                    let uu____17928 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____17928 with
                     | (head_p,args_p) ->
                         let uu____17971 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____17971
                         then
                           let uu____17974 =
                             let uu____17975 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____17975.FStar_Syntax_Syntax.n  in
                           (match uu____17974 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____17980 =
                                    let uu____17982 =
                                      let uu____17984 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____17984
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____17982
                                     in
                                  if uu____17980
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____18012 =
                                    let uu____18037 =
                                      let uu____18041 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18041
                                       in
                                    match uu____18037 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18090 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18090 with
                                         | (params_p,uu____18148) ->
                                             let uu____18189 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18189 with
                                              | (params_s,uu____18247) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____18012 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18376  ->
                                             fun uu____18377  ->
                                               match (uu____18376,
                                                       uu____18377)
                                               with
                                               | ((p,uu____18411),(s,uu____18413))
                                                   ->
                                                   let uu____18446 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18446 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18449 =
                                                          let uu____18451 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18453 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18451
                                                            uu____18453
                                                           in
                                                        fail2 uu____18449
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
                            | uu____18458 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18462 =
                              let uu____18464 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18466 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18464 uu____18466
                               in
                            fail2 uu____18462))
                | uu____18469 ->
                    let uu____18470 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18470 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18507 = FStar_Syntax_Util.head_and_args e  in
          match uu____18507 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18571 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18571 with
                    | (us,t_f) ->
                        let uu____18588 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18588 with
                         | (formals,t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18717 formals1 args1 =
                                 match uu____18717 with
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
                                          let uu____18862 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____18862, bvs, guard)
                                      | ((f1,uu____18868)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____18926 =
                                            let uu____18947 =
                                              let uu____18948 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____18948.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18947 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2423_18973 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2423_18973.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2423_18973.FStar_Syntax_Syntax.index);
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
                                                uu____18996 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____19010 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____19010 with
                                                 | (a1,uu____19038,g) ->
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
                                            | uu____19062 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____18926 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19124 =
                                                 let uu____19147 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19147)
                                                  in
                                               aux uu____19124 formals2 args2)
                                      | uu____19186 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19242 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19291 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19291
           then
             let uu____19296 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19298 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19296
               uu____19298
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19313 ->
               let uu____19320 =
                 let uu____19322 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19322
                  in
               failwith uu____19320
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2455_19337 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2455_19337.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2455_19337.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19338 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19338,
                 (let uu___2458_19342 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2458_19342.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2462_19345 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2462_19345.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2462_19345.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19346 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19346,
                 (let uu___2465_19350 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2465_19350.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19351 ->
               let uu____19352 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19352 with
                | (uu____19374,e_c,uu____19376,uu____19377) ->
                    let uu____19382 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19382 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____19405 =
                              let uu____19407 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t
                                 in
                              Prims.op_Negation uu____19407  in
                            if uu____19405
                            then
                              let uu____19410 =
                                let uu____19412 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____19414 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19412 uu____19414
                                 in
                              fail1 uu____19410
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19472  ->
                        match uu____19472 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19502
                                 -> (p1, b)
                             | uu____19512 ->
                                 let uu____19513 =
                                   let uu____19516 =
                                     let uu____19517 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____19517
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____19516
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____19513, b))) sub_pats
                    in
                 let uu___2493_19521 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2493_19521.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19566  ->
                         match uu____19566 with
                         | (x,uu____19576) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19584
                                  -> false
                              | uu____19592 -> true)))
                  in
               let uu____19594 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____19594 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19631 =
                          let uu____19633 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____19635 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____19637 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____19644 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19633 uu____19635 uu____19637 uu____19644
                           in
                        failwith uu____19631)
                     else ();
                     (let uu____19649 =
                        let uu____19658 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____19658 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard) ->
                            let g' =
                              let uu____19686 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____19686  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____19689 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____19689
                              then
                                let uu____19694 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____19696 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____19698 =
                                  let uu____19700 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____19708 =
                                           let uu____19710 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____19712 =
                                             let uu____19714 =
                                               let uu____19716 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____19716 ")"
                                                in
                                             Prims.op_Hat " : " uu____19714
                                              in
                                           Prims.op_Hat uu____19710
                                             uu____19712
                                            in
                                         Prims.op_Hat "(" uu____19708)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____19700
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19694 uu____19696 uu____19698
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1))
                         in
                      match uu____19649 with
                      | (simple_pat_e1,simple_bvs1,g1) ->
                          let uu____19748 =
                            let uu____19770 =
                              let uu____19792 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], uu____19792)  in
                            FStar_List.fold_left2
                              (fun uu____19853  ->
                                 fun uu____19854  ->
                                   fun x  ->
                                     match (uu____19853, uu____19854) with
                                     | ((env2,bvs,pats,subst1,g),(p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____19987 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____19987 with
                                          | (bvs_p,e_p,p2,g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let uu____20028 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20028))) uu____19770
                              sub_pats1 simple_bvs1
                             in
                          (match uu____19748 with
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
                                              let uu___2565_20240 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2565_20240.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____20245 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____20245
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____20289)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20326 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____20326
                                             | uu____20346 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20372 ->
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
                                     let uu___2586_20415 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2586_20415.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20427 -> failwith "Impossible"  in
                               let uu____20431 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, pat_e, uu____20431, g))))))
           in
        (let uu____20435 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____20435
         then
           let uu____20440 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20440
         else ());
        (let uu____20445 =
           let uu____20456 =
             let uu___2591_20457 =
               let uu____20458 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____20458 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2591_20457.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2591_20457.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2591_20457.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2591_20457.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2591_20457.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2591_20457.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2591_20457.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2591_20457.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2591_20457.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2591_20457.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2591_20457.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2591_20457.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2591_20457.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2591_20457.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2591_20457.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2591_20457.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2591_20457.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2591_20457.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2591_20457.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2591_20457.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2591_20457.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2591_20457.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2591_20457.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2591_20457.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2591_20457.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2591_20457.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2591_20457.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2591_20457.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2591_20457.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2591_20457.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2591_20457.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2591_20457.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2591_20457.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2591_20457.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2591_20457.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2591_20457.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2591_20457.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2591_20457.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2591_20457.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2591_20457.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2591_20457.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2591_20457.FStar_TypeChecker_Env.nbe)
             }  in
           let uu____20474 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____20456 uu____20474 pat_t  in
         match uu____20445 with
         | (bvs,pat_e,pat,g) ->
             ((let uu____20498 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____20498
               then
                 let uu____20503 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____20505 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20503
                   uu____20505
               else ());
              (let uu____20510 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____20511 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, uu____20510, pat_e, uu____20511, g))))

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
        let uu____20557 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____20557 with
        | (pattern,when_clause,branch_exp) ->
            let uu____20603 = branch1  in
            (match uu____20603 with
             | (cpat,uu____20645,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____20667 =
                   let uu____20674 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____20674
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____20667 with
                  | (scrutinee_env,uu____20708) ->
                      let uu____20713 = tc_pat env pat_t pattern  in
                      (match uu____20713 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp,guard_pat)
                           ->
                           let uu____20764 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____20794 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____20794
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____20817 =
                                      let uu____20824 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____20824 e  in
                                    match uu____20817 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____20764 with
                            | (when_clause1,g_when) ->
                                let uu____20878 = tc_term pat_env branch_exp
                                   in
                                (match uu____20878 with
                                 | (branch_exp1,c,g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____20934 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _20945  ->
                                                  FStar_Pervasives_Native.Some
                                                    _20945) uu____20934
                                          in
                                       let uu____20946 =
                                         let eqs =
                                           let uu____20968 =
                                             let uu____20970 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____20970
                                              in
                                           if uu____20968
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____20986 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____21001 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____21004 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____21007 ->
                                                  let uu____21008 =
                                                    let uu____21011 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____21011 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____21008)
                                            in
                                         let uu____21014 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch
                                            in
                                         match uu____21014 with
                                         | (c1,g_branch1) ->
                                             let uu____21041 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____21058 when
                                                   let uu____21071 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____21071
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
                                                   let uu____21102 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____21103 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____21102, uu____21103)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____21124 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21124
                                                      in
                                                   let uu____21125 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____21126 =
                                                     let uu____21127 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21127 g_when
                                                      in
                                                   (uu____21125, uu____21126)
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
                                                   let uu____21145 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____21145, g_when)
                                                in
                                             (match uu____21041 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21188 =
                                                        should_return1 &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____21188
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____21193 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  let uu____21194 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21193, uu____21194))
                                          in
                                       match uu____20946 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21245 =
                                               let uu____21247 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____21247
                                                in
                                             if uu____21245
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21301 =
                                                      let uu____21309 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21309
                                                       in
                                                    match uu____21301 with
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
                                                          let uu____21325 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator
                                                             in
                                                          (match uu____21325
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> []
                                                           | uu____21346 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let disc1 =
                                                                 let uu____21362
                                                                   =
                                                                   let uu____21367
                                                                    =
                                                                    let uu____21368
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____21368]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21367
                                                                    in
                                                                 uu____21362
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let uu____21393
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool
                                                                  in
                                                               [uu____21393])
                                                        else []
                                                     in
                                                  let fail1 uu____21401 =
                                                    let uu____21402 =
                                                      let uu____21404 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____21406 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____21408 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21404
                                                        uu____21406
                                                        uu____21408
                                                       in
                                                    failwith uu____21402  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____21423) ->
                                                        head_constructor t1
                                                    | uu____21428 -> fail1 ()
                                                     in
                                                  let force_scrutinee
                                                    uu____21434 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____21435 =
                                                          let uu____21437 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p
                                                             in
                                                          let uu____21439 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2
                                                             in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21437
                                                            uu____21439
                                                           in
                                                        failwith uu____21435
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t
                                                     in
                                                  let pat_exp2 =
                                                    let uu____21446 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____21446
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21451,FStar_Syntax_Syntax.Tm_name
                                                     uu____21452) -> []
                                                  | (uu____21453,FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     )) -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21456 =
                                                        let uu____21457 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        let uu____21458 =
                                                          force_scrutinee ()
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21457
                                                          uu____21458
                                                          pat_exp2
                                                         in
                                                      [uu____21456]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21459,FStar_Pervasives_Native.Some
                                                      uu____21460)),uu____21461)
                                                      ->
                                                      let uu____21478 =
                                                        let uu____21485 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env
                                                           in
                                                        match uu____21485
                                                        with
                                                        | (env1,uu____21499)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2
                                                         in
                                                      (match uu____21478 with
                                                       | (uu____21506,t,uu____21508)
                                                           ->
                                                           let uu____21509 =
                                                             let uu____21510
                                                               =
                                                               force_scrutinee
                                                                 ()
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21510
                                                               pat_exp2
                                                              in
                                                           [uu____21509])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21511,[]),FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21512) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21536 =
                                                        let uu____21538 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21538
                                                         in
                                                      if uu____21536
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21548 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21551 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21548
                                                           uu____21551)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21554,[]),FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21555) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21573 =
                                                        let uu____21575 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21575
                                                         in
                                                      if uu____21573
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21585 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21588 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21585
                                                           uu____21588)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21591,pat_args),FStar_Syntax_Syntax.Tm_app
                                                     (head1,args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____21638 =
                                                        (let uu____21642 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____21642)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args))
                                                         in
                                                      if uu____21638
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21670 =
                                                             let uu____21675
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____21675
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____21761
                                                                     ->
                                                                    match uu____21761
                                                                    with
                                                                    | 
                                                                    ((pi,uu____21783),
                                                                    (ei,uu____21785))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____21813
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____21813
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____21834
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____21846
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____21846
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____21848
                                                                    =
                                                                    let uu____21849
                                                                    =
                                                                    let uu____21854
                                                                    =
                                                                    let uu____21855
                                                                    =
                                                                    let uu____21864
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____21864
                                                                     in
                                                                    [uu____21855]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____21854
                                                                     in
                                                                    uu____21849
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____21848
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____21670
                                                             FStar_List.flatten
                                                            in
                                                         let uu____21887 =
                                                           let uu____21890 =
                                                             force_scrutinee
                                                               ()
                                                              in
                                                           discriminate
                                                             uu____21890 f
                                                            in
                                                         FStar_List.append
                                                           uu____21887
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____21893,uu____21894)
                                                      -> []
                                                  | uu____21901 ->
                                                      let uu____21906 =
                                                        let uu____21908 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2
                                                           in
                                                        let uu____21910 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2
                                                           in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____21908
                                                          uu____21910
                                                         in
                                                      failwith uu____21906
                                                   in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____21939 =
                                                    let uu____21941 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____21941
                                                     in
                                                  if uu____21939
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____21947 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____21947
                                                        in
                                                     let uu____21956 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____21956 with
                                                     | (k,uu____21962) ->
                                                         let uu____21963 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____21963
                                                          with
                                                          | (t1,uu____21971,uu____21972)
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
                                           ((let uu____21984 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____21984
                                             then
                                               let uu____21987 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____21987
                                             else ());
                                            (let uu____21993 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____22010 =
                                               let uu____22011 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____22011 guard
                                                in
                                             (uu____21993, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____22010))))))))))

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
          let uu____22058 = check_let_bound_def true env1 lb  in
          (match uu____22058 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____22084 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____22106 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____22106, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22112 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____22112
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____22113 =
                      let uu____22126 =
                        let uu____22141 =
                          let uu____22150 =
                            let uu____22157 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____22157)
                             in
                          [uu____22150]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____22141
                         in
                      FStar_List.hd uu____22126  in
                    match uu____22113 with
                    | (uu____22193,univs1,e11,c11,gvs) ->
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
                        let uu____22207 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____22207))
                  in
               (match uu____22084 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____22224 =
                      let uu____22233 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____22233
                      then
                        let uu____22244 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____22244 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22278 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____22278
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22279 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____22279, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____22294 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____22294
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____22300 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____22300
                            then e2
                            else
                              ((let uu____22308 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____22308
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
                    (match uu____22224 with
                     | (e21,c12) ->
                         ((let uu____22332 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____22332
                           then
                             let uu____22335 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22335
                           else ());
                          (let e12 =
                             let uu____22341 = FStar_Options.tcnorm ()  in
                             if uu____22341
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
                           (let uu____22347 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____22347
                            then
                              let uu____22350 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22350
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
                            let uu____22359 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____22373 =
                              FStar_Syntax_Util.lcomp_of_comp cres  in
                            (uu____22359, uu____22373,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22374 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____22385 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____22385
        then
          let universe_of_binders bs =
            let uu____22412 =
              FStar_List.fold_left
                (fun uu____22437  ->
                   fun b  ->
                     match uu____22437 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____22412 with | (uu____22485,us) -> FStar_List.rev us
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
            let uu___2903_22521 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2903_22521.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2903_22521.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2903_22521.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2903_22521.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2903_22521.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2903_22521.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2903_22521.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2903_22521.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2903_22521.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2903_22521.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2903_22521.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2903_22521.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2903_22521.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2903_22521.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2903_22521.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2903_22521.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2903_22521.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2903_22521.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2903_22521.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2903_22521.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2903_22521.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2903_22521.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2903_22521.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2903_22521.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2903_22521.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2903_22521.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2903_22521.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2903_22521.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2903_22521.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2903_22521.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2903_22521.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2903_22521.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2903_22521.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2903_22521.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2903_22521.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2903_22521.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2903_22521.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2903_22521.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2903_22521.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2903_22521.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2903_22521.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2903_22521.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____22523 =
            let uu____22535 =
              let uu____22536 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____22536 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____22535 lb  in
          (match uu____22523 with
           | (e1,uu____22559,c1,g1,annotated) ->
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
                  (let uu____22573 =
                     let uu____22579 =
                       let uu____22581 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____22583 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____22581 uu____22583
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____22579)
                      in
                   FStar_Errors.raise_error uu____22573
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____22594 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_Syntax_Syntax.res_typ)
                      in
                   if uu____22594
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___2918_22606 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2918_22606.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2918_22606.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____22607 =
                   let uu____22612 =
                     let uu____22613 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____22613]  in
                   FStar_Syntax_Subst.open_term uu____22612 e2  in
                 match uu____22607 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____22657 = tc_term env_x e21  in
                     (match uu____22657 with
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
                            let uu____22683 =
                              let uu____22690 =
                                let uu____22691 =
                                  let uu____22705 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____22705)  in
                                FStar_Syntax_Syntax.Tm_let uu____22691  in
                              FStar_Syntax_Syntax.mk uu____22690  in
                            uu____22683 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____22723 =
                              let uu____22724 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____22725 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____22724
                                c1.FStar_Syntax_Syntax.res_typ uu____22725
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _22726  ->
                                 FStar_TypeChecker_Common.NonTrivial _22726)
                              uu____22723
                             in
                          let g21 =
                            let uu____22728 =
                              let uu____22729 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____22729 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____22728
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____22732 =
                            let uu____22734 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____22734  in
                          if uu____22732
                          then
                            let tt =
                              let uu____22745 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____22745
                                FStar_Option.get
                               in
                            ((let uu____22751 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____22751
                              then
                                let uu____22756 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____22758 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____22756 uu____22758
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____22765 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____22765 with
                             | (t,g_ex) ->
                                 ((let uu____22779 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____22779
                                   then
                                     let uu____22784 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____22786 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____22784 uu____22786
                                   else ());
                                  (let uu____22791 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___2951_22793 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___2951_22793.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___2951_22793.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___2951_22793.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____22791))))))))
      | uu____22794 ->
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
          let uu____22830 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____22830 with
           | (lbs1,e21) ->
               let uu____22849 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____22849 with
                | (env0,topt) ->
                    let uu____22868 = build_let_rec_env true env0 lbs1  in
                    (match uu____22868 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____22891 = check_let_recs rec_env lbs2  in
                         (match uu____22891 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____22911 =
                                  let uu____22912 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____22912
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____22911
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____22918 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____22918
                                  (fun _22935  ->
                                     FStar_Pervasives_Native.Some _22935)
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
                                     let uu____22972 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____23006 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____23006)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____22972
                                      in
                                   FStar_List.map2
                                     (fun uu____23041  ->
                                        fun lb  ->
                                          match uu____23041 with
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
                                let uu____23089 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____23089
                                 in
                              let uu____23090 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____23090 with
                               | (lbs5,e22) ->
                                   ((let uu____23110 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____23110
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23111 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____23111, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23125 -> failwith "Impossible"

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
          let uu____23161 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23161 with
           | (lbs1,e21) ->
               let uu____23180 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23180 with
                | (env0,topt) ->
                    let uu____23199 = build_let_rec_env false env0 lbs1  in
                    (match uu____23199 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23222 =
                           let uu____23229 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____23229
                             (fun uu____23252  ->
                                match uu____23252 with
                                | (lbs3,g) ->
                                    let uu____23271 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____23271))
                            in
                         (match uu____23222 with
                          | (lbs3,g_lbs) ->
                              let uu____23286 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3026_23309 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3026_23309.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3026_23309.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3029_23311 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3029_23311.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____23286 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____23338 = tc_term env2 e21  in
                                   (match uu____23338 with
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
                                          let uu____23362 =
                                            let uu____23363 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23363 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23362
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
                                          let uu___3050_23373 = cres4  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___3050_23373.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___3050_23373.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___3050_23373.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____23381 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____23381))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____23382 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____23382 with
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
                                                  uu____23423 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____23424 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____23424 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3066_23438
                                                           = cres5  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___3066_23438.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___3066_23438.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___3066_23438.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____23439 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____23439))))))))))
      | uu____23440 -> failwith "Impossible"

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
          let uu____23488 = FStar_Options.ml_ish ()  in
          if uu____23488
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____23496 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____23496 with
             | (formals,c) ->
                 let uu____23528 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____23528 with
                  | (actuals,uu____23539,uu____23540) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____23561 =
                          let uu____23567 =
                            let uu____23569 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____23571 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____23569 uu____23571
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____23567)
                           in
                        FStar_Errors.raise_error uu____23561
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____23579 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____23579 actuals
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
                                (let uu____23610 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____23610)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____23629 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____23629)
                               in
                            let msg =
                              let uu____23634 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____23636 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____23634 uu____23636 formals_msg
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
        let uu____23648 =
          FStar_List.fold_left
            (fun uu____23681  ->
               fun lb  ->
                 match uu____23681 with
                 | (lbs1,env1,g_acc) ->
                     let uu____23706 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____23706 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____23729 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____23748 =
                                 let uu____23755 =
                                   let uu____23756 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____23756
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3112_23767 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3112_23767.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3112_23767.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3112_23767.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3112_23767.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3112_23767.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3112_23767.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3112_23767.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3112_23767.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3112_23767.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3112_23767.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3112_23767.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3112_23767.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3112_23767.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3112_23767.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3112_23767.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3112_23767.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3112_23767.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3112_23767.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3112_23767.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3112_23767.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3112_23767.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3112_23767.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3112_23767.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3112_23767.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3112_23767.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3112_23767.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3112_23767.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3112_23767.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3112_23767.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3112_23767.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3112_23767.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3112_23767.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3112_23767.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3112_23767.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3112_23767.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3112_23767.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3112_23767.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3112_23767.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3112_23767.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3112_23767.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3112_23767.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3112_23767.FStar_TypeChecker_Env.nbe)
                                    }) t uu____23755
                                  in
                               match uu____23748 with
                               | (t1,uu____23776,g) ->
                                   let uu____23778 =
                                     let uu____23779 =
                                       let uu____23780 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____23780
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____23779
                                      in
                                   let uu____23781 = norm env01 t1  in
                                   (uu____23778, uu____23781))
                             in
                          (match uu____23729 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____23801 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____23801
                                 then
                                   let uu___3122_23804 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3122_23804.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3122_23804.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3122_23804.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3122_23804.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3122_23804.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3122_23804.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3122_23804.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3122_23804.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3122_23804.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3122_23804.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3122_23804.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3122_23804.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3122_23804.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3122_23804.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3122_23804.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3122_23804.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3122_23804.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3122_23804.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3122_23804.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3122_23804.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3122_23804.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3122_23804.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3122_23804.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3122_23804.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3122_23804.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3122_23804.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3122_23804.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3122_23804.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3122_23804.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3122_23804.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3122_23804.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3122_23804.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3122_23804.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3122_23804.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3122_23804.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3122_23804.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3122_23804.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3122_23804.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3122_23804.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3122_23804.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3122_23804.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3122_23804.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3125_23818 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3125_23818.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3125_23818.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3125_23818.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3125_23818.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____23648 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____23844 =
        let uu____23853 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____23879 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____23879 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____23909 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____23909
                       | uu____23916 ->
                           let lb1 =
                             let uu___3142_23919 = lb  in
                             let uu____23920 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____23920;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3142_23919.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____23923 =
                             let uu____23930 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____23930
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____23923 with
                            | (e,c,g) ->
                                ((let uu____23939 =
                                    let uu____23941 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____23941  in
                                  if uu____23939
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
        FStar_All.pipe_right uu____23853 FStar_List.unzip  in
      match uu____23844 with
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
        let uu____23997 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____23997 with
        | (env1,uu____24016) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____24024 = check_lbtyp top_level env lb  in
            (match uu____24024 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____24073 =
                     tc_maybe_toplevel_term
                       (let uu___3173_24082 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3173_24082.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3173_24082.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3173_24082.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3173_24082.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3173_24082.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3173_24082.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3173_24082.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3173_24082.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3173_24082.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3173_24082.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3173_24082.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3173_24082.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3173_24082.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3173_24082.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3173_24082.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3173_24082.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3173_24082.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3173_24082.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3173_24082.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3173_24082.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3173_24082.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3173_24082.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3173_24082.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3173_24082.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3173_24082.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3173_24082.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3173_24082.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3173_24082.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3173_24082.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3173_24082.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3173_24082.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3173_24082.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3173_24082.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3173_24082.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3173_24082.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3173_24082.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3173_24082.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3173_24082.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3173_24082.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3173_24082.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3173_24082.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3173_24082.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____24073 with
                   | (e12,c1,g1) ->
                       let uu____24097 =
                         let uu____24102 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24108  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____24102 e12 c1 wf_annot
                          in
                       (match uu____24097 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____24125 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____24125
                              then
                                let uu____24128 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____24130 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____24132 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24128 uu____24130 uu____24132
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
            let uu____24171 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24171 with
             | (univ_opening,univ_vars1) ->
                 let uu____24204 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24204))
        | uu____24209 ->
            let uu____24210 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24210 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24260 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24260)
                 else
                   (let uu____24267 = FStar_Syntax_Util.type_u ()  in
                    match uu____24267 with
                    | (k,uu____24287) ->
                        let uu____24288 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____24288 with
                         | (t2,uu____24310,g) ->
                             ((let uu____24313 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____24313
                               then
                                 let uu____24316 =
                                   let uu____24318 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____24318
                                    in
                                 let uu____24319 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24316 uu____24319
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____24325 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24325))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____24331  ->
      match uu____24331 with
      | (x,imp) ->
          let uu____24358 = FStar_Syntax_Util.type_u ()  in
          (match uu____24358 with
           | (tu,u) ->
               ((let uu____24380 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____24380
                 then
                   let uu____24383 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____24385 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____24387 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____24383 uu____24385 uu____24387
                 else ());
                (let uu____24392 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____24392 with
                 | (t,uu____24414,g) ->
                     let uu____24416 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____24432 = tc_tactic env tau  in
                           (match uu____24432 with
                            | (tau1,uu____24446,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____24450 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____24416 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3235_24485 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3235_24485.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3235_24485.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____24487 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____24487
                            then
                              let uu____24490 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____24494 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____24490
                                uu____24494
                            else ());
                           (let uu____24499 = push_binding env x1  in
                            (x1, uu____24499, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____24511 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____24511
       then
         let uu____24514 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____24514
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____24627 = tc_binder env1 b  in
             (match uu____24627 with
              | (b1,env',g,u) ->
                  let uu____24676 = aux env' bs2  in
                  (match uu____24676 with
                   | (bs3,env'1,g',us) ->
                       let uu____24737 =
                         let uu____24738 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____24738  in
                       ((b1 :: bs3), env'1, uu____24737, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.args Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Env.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____24836  ->
             fun uu____24837  ->
               match (uu____24836, uu____24837) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____24929 = tc_term en1 t  in
                     match uu____24929 with
                     | (t1,uu____24949,g') ->
                         let uu____24951 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____24951)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____25005  ->
             match uu____25005 with
             | (pats1,g) ->
                 let uu____25032 = tc_args en p  in
                 (match uu____25032 with
                  | (args,g') ->
                      let uu____25045 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____25045))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____25058 = tc_maybe_toplevel_term env e  in
      match uu____25058 with
      | (e1,c,g) ->
          let uu____25074 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____25074
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____25088 =
               let uu____25094 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____25094
               then
                 let uu____25102 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____25102, false)
               else
                 (let uu____25107 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____25107, true))
                in
             match uu____25088 with
             | (target_comp,allow_ghost) ->
                 let uu____25120 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____25120 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____25130 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____25131 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____25130, uu____25131)
                  | uu____25132 ->
                      if allow_ghost
                      then
                        let uu____25142 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____25142
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____25156 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____25156
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
      let uu____25180 = tc_tot_or_gtot_term env t  in
      match uu____25180 with
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
      (let uu____25213 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25213
       then
         let uu____25218 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____25218
       else ());
      (let env1 =
         let uu___3317_25224 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3317_25224.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3317_25224.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3317_25224.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3317_25224.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3317_25224.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3317_25224.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3317_25224.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3317_25224.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3317_25224.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3317_25224.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3317_25224.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3317_25224.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3317_25224.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3317_25224.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3317_25224.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3317_25224.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3317_25224.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3317_25224.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3317_25224.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3317_25224.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3317_25224.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3317_25224.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3317_25224.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3317_25224.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3317_25224.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3317_25224.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3317_25224.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3317_25224.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3317_25224.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3317_25224.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3317_25224.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3317_25224.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3317_25224.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3317_25224.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3317_25224.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3317_25224.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3317_25224.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3317_25224.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3317_25224.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3317_25224.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3317_25224.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____25232 =
         try
           (fun uu___3321_25246  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____25267) ->
             let uu____25270 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____25270
          in
       match uu____25232 with
       | (t,c,g) ->
           let uu____25287 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____25287
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____25298 =
                let uu____25304 =
                  let uu____25306 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25306
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25304)
                 in
              let uu____25310 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____25298 uu____25310))
  
let level_of_type_fail :
  'Auu____25326 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25326
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____25344 =
          let uu____25350 =
            let uu____25352 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____25352 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25350)  in
        let uu____25356 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____25344 uu____25356
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____25390 =
            let uu____25391 = FStar_Syntax_Util.unrefine t1  in
            uu____25391.FStar_Syntax_Syntax.n  in
          match uu____25390 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____25395 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____25401 = FStar_Syntax_Util.type_u ()  in
                 match uu____25401 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3352_25409 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3352_25409.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3352_25409.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3352_25409.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3352_25409.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3352_25409.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3352_25409.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3352_25409.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3352_25409.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3352_25409.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3352_25409.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3352_25409.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3352_25409.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3352_25409.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3352_25409.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3352_25409.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3352_25409.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3352_25409.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3352_25409.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3352_25409.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3352_25409.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3352_25409.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3352_25409.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3352_25409.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3352_25409.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3352_25409.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3352_25409.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3352_25409.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3352_25409.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3352_25409.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3352_25409.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3352_25409.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3352_25409.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3352_25409.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3352_25409.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3352_25409.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3352_25409.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3352_25409.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3352_25409.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3352_25409.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3352_25409.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3352_25409.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3352_25409.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25414 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____25414
                       | uu____25416 ->
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
      let uu____25433 =
        let uu____25434 = FStar_Syntax_Subst.compress e  in
        uu____25434.FStar_Syntax_Syntax.n  in
      match uu____25433 with
      | FStar_Syntax_Syntax.Tm_bvar uu____25437 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____25440 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____25464 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____25481) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____25526) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____25533 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25533 with | ((uu____25542,t),uu____25544) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____25550 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____25550
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25553,(FStar_Util.Inl t,uu____25555),uu____25556) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25603,(FStar_Util.Inr c,uu____25605),uu____25606) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____25654 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____25663;
             FStar_Syntax_Syntax.vars = uu____25664;_},us)
          ->
          let uu____25670 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25670 with
           | ((us',t),uu____25681) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____25688 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____25688)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____25707 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____25709 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____25718) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____25745 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____25745 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____25765  ->
                      match uu____25765 with
                      | (b,uu____25773) ->
                          let uu____25778 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____25778) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____25783 = universe_of_aux env res  in
                 level_of_type env res uu____25783  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____25894 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____25910 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____25948 ->
                let uu____25949 = universe_of_aux env hd3  in
                (uu____25949, args1)
            | FStar_Syntax_Syntax.Tm_name uu____25960 ->
                let uu____25961 = universe_of_aux env hd3  in
                (uu____25961, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____25972 ->
                let uu____25985 = universe_of_aux env hd3  in
                (uu____25985, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____25996 ->
                let uu____26003 = universe_of_aux env hd3  in
                (uu____26003, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____26014 ->
                let uu____26041 = universe_of_aux env hd3  in
                (uu____26041, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____26052 ->
                let uu____26059 = universe_of_aux env hd3  in
                (uu____26059, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____26070 ->
                let uu____26071 = universe_of_aux env hd3  in
                (uu____26071, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____26082 ->
                let uu____26097 = universe_of_aux env hd3  in
                (uu____26097, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26108 ->
                let uu____26115 = universe_of_aux env hd3  in
                (uu____26115, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26126 ->
                let uu____26127 = universe_of_aux env hd3  in
                (uu____26127, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26138,hd4::uu____26140) ->
                let uu____26205 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____26205 with
                 | (uu____26220,uu____26221,hd5) ->
                     let uu____26239 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____26239 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____26296 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____26298 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____26298 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____26356 ->
                let uu____26357 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____26357 with
                 | (env1,uu____26379) ->
                     let env2 =
                       let uu___3513_26385 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3513_26385.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3513_26385.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3513_26385.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3513_26385.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3513_26385.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3513_26385.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3513_26385.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3513_26385.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3513_26385.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3513_26385.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3513_26385.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3513_26385.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3513_26385.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3513_26385.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3513_26385.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3513_26385.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3513_26385.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3513_26385.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3513_26385.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3513_26385.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3513_26385.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3513_26385.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3513_26385.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3513_26385.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3513_26385.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3513_26385.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3513_26385.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3513_26385.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3513_26385.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3513_26385.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3513_26385.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3513_26385.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3513_26385.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3513_26385.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3513_26385.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3513_26385.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3513_26385.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3513_26385.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3513_26385.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3513_26385.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____26390 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____26390
                       then
                         let uu____26395 =
                           let uu____26397 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____26397  in
                         let uu____26398 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____26395 uu____26398
                       else ());
                      (let uu____26403 = tc_term env2 hd3  in
                       match uu____26403 with
                       | (uu____26424,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____26425;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____26427;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____26428;_},g)
                           ->
                           ((let uu____26442 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____26442 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____26453 = type_of_head true hd1 args  in
          (match uu____26453 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____26492 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____26492 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____26544 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____26544)))
      | FStar_Syntax_Syntax.Tm_match (uu____26546,hd1::uu____26548) ->
          let uu____26613 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____26613 with
           | (uu____26614,uu____26615,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____26633,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____26680 = universe_of_aux env e  in
      level_of_type env e uu____26680
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____26704 = tc_binders env tps  in
      match uu____26704 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____26762 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____26788 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26794 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____26794
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26796 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26796
            (fun uu____26810  ->
               match uu____26810 with
               | (t2,uu____26818) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26820;
             FStar_Syntax_Syntax.vars = uu____26821;_},us)
          ->
          let uu____26827 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26827
            (fun uu____26841  ->
               match uu____26841 with
               | (t2,uu____26849) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____26850) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____26852 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____26852
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____26854 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____26854
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____26859;_})
          ->
          let mk_comp =
            let uu____26903 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____26903
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____26934 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____26934
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____27004 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____27004
                 (fun u  ->
                    let uu____27012 =
                      let uu____27015 =
                        let uu____27022 =
                          let uu____27023 =
                            let uu____27038 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____27038)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____27023  in
                        FStar_Syntax_Syntax.mk uu____27022  in
                      uu____27015 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____27012))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27075 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27075 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27134 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____27134
                       (fun uc  ->
                          let uu____27142 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____27142)
                 | (x,imp)::bs3 ->
                     let uu____27168 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____27168
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27177 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27197) ->
          let uu____27202 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____27202
            (fun u_x  ->
               let uu____27210 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____27210)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27215;
             FStar_Syntax_Syntax.vars = uu____27216;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27295 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27295 with
           | (unary_op1,uu____27315) ->
               let head1 =
                 let uu____27343 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27343
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
             FStar_Syntax_Syntax.pos = uu____27391;
             FStar_Syntax_Syntax.vars = uu____27392;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27488 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27488 with
           | (unary_op1,uu____27508) ->
               let head1 =
                 let uu____27536 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____27536
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
             FStar_Syntax_Syntax.pos = uu____27592;
             FStar_Syntax_Syntax.vars = uu____27593;_},uu____27594::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____27633;
             FStar_Syntax_Syntax.vars = uu____27634;_},(t2,uu____27636)::uu____27637::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____27733 =
              let uu____27734 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____27734.FStar_Syntax_Syntax.n  in
            match uu____27733 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____27807 = FStar_Util.first_N n_args bs  in
                    match uu____27807 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____27895 =
                          let uu____27900 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____27900  in
                        (match uu____27895 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____27954 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____27954 with
                       | (bs1,c1) ->
                           let uu____27975 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____27975
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____28057  ->
                     match uu____28057 with
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
                         let uu____28133 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____28133)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____28135) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____28141,uu____28142) ->
                aux t2
            | uu____28183 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28184,(FStar_Util.Inl t2,uu____28186),uu____28187) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28234,(FStar_Util.Inr c,uu____28236),uu____28237) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____28302 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____28302
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____28310) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28315 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28338 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____28352 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____28363 = type_of_well_typed_term env t  in
      match uu____28363 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____28369;
            FStar_Syntax_Syntax.vars = uu____28370;_}
          -> FStar_Pervasives_Native.Some u
      | uu____28373 -> FStar_Pervasives_Native.None

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
            let uu___3792_28401 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3792_28401.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3792_28401.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3792_28401.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3792_28401.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3792_28401.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3792_28401.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3792_28401.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3792_28401.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3792_28401.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3792_28401.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3792_28401.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3792_28401.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3792_28401.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3792_28401.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3792_28401.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3792_28401.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3792_28401.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3792_28401.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3792_28401.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3792_28401.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3792_28401.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3792_28401.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3792_28401.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3792_28401.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3792_28401.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3792_28401.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3792_28401.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3792_28401.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3792_28401.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3792_28401.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3792_28401.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3792_28401.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3792_28401.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3792_28401.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3792_28401.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3792_28401.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3792_28401.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3792_28401.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3792_28401.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3792_28401.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3792_28401.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3792_28401.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28408 =
            if must_total
            then
              let uu____28410 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28410 with | (uu____28417,uu____28418,g) -> g
            else
              (let uu____28422 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28422 with | (uu____28429,uu____28430,g) -> g)
             in
          let uu____28432 = type_of_well_typed_term env2 t  in
          match uu____28432 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____28437 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____28437
                then
                  let uu____28442 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____28444 = FStar_Syntax_Print.term_to_string t  in
                  let uu____28446 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____28448 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____28442 uu____28444 uu____28446 uu____28448
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____28457 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____28457
                 then
                   let uu____28462 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____28464 = FStar_Syntax_Print.term_to_string t  in
                   let uu____28466 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____28468 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____28462
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____28464 uu____28466 uu____28468
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
            let uu___3823_28505 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3823_28505.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3823_28505.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3823_28505.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3823_28505.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3823_28505.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3823_28505.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3823_28505.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3823_28505.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3823_28505.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3823_28505.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3823_28505.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3823_28505.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3823_28505.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3823_28505.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3823_28505.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3823_28505.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3823_28505.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3823_28505.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3823_28505.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3823_28505.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3823_28505.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3823_28505.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3823_28505.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3823_28505.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3823_28505.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3823_28505.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3823_28505.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3823_28505.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3823_28505.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3823_28505.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3823_28505.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3823_28505.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3823_28505.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3823_28505.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3823_28505.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3823_28505.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3823_28505.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3823_28505.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3823_28505.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3823_28505.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3823_28505.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3823_28505.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28512 =
            if must_total
            then
              let uu____28514 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28514 with | (uu____28521,uu____28522,g) -> g
            else
              (let uu____28526 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28526 with | (uu____28533,uu____28534,g) -> g)
             in
          let uu____28536 =
            let uu____28538 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____28538  in
          if uu____28536
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  