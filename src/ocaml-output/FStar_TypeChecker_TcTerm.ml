open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___8_5 = env in
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
  fun env ->
    let uu___11_13 = env in
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
  fun vs ->
    FStar_List.fold_right
      (fun v1 ->
         fun tl1 ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos in
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl1 in [uu____75] in
               uu____55 :: uu____64 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____54 in
           uu____49 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_116 ->
    match uu___0_116 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> true
    | uu____121 -> false
let steps :
  'Auu____130 . 'Auu____130 -> FStar_TypeChecker_Env.step Prims.list =
  fun env ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env -> fun t -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun c -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun head_opt ->
    fun env ->
      fun fvs ->
        fun kt ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____218 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____232 =
                  FStar_List.tryFind (fun x -> FStar_Util.set_mem x fvs') fvs in
                (match uu____232 with
                 | FStar_Pervasives_Native.None ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____267 uu____269 in
                          let uu____272 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____272 in
                        let uu____278 =
                          let uu____291 = FStar_TypeChecker_Env.get_range env in
                          let uu____292 =
                            let uu____293 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____293 in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____291 env uu____292 in
                        match uu____278 with
                        | (s, uu____308, g0) ->
                            let uu____322 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s in
                            (match uu____322 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____332 =
                                     FStar_TypeChecker_Env.conj_guard g g0 in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____332 in
                                 (s, g1)
                             | uu____333 -> fail1 ()))) in
          aux false kt
let push_binding :
  'Auu____344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____344) -> FStar_TypeChecker_Env.env
  =
  fun env ->
    fun b ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s ->
    fun b ->
      fun v1 ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let (set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp)
  =
  fun lc ->
    fun t ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____425 ->
           let uu____426 = FStar_Syntax_Syntax.lcomp_comp lc in
           FStar_Syntax_Util.set_result_typ uu____426 t)
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> e
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun tlc ->
        fun guard ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____485 = FStar_Syntax_Syntax.mk_Total t in
                 FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                   uu____485
             | FStar_Util.Inr lc -> lc in
           let t = lc.FStar_Syntax_Syntax.res_typ in
           let uu____488 =
             let uu____495 = FStar_TypeChecker_Env.expected_typ env in
             match uu____495 with
             | FStar_Pervasives_Native.None -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____505 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t' in
                 (match uu____505 with
                  | (e1, lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____519 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____519 with
                       | (e2, g) ->
                           ((let uu____533 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____533
                             then
                               let uu____536 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____538 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____540 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____542 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____536 uu____538 uu____540 uu____542
                             else ());
                            (let msg =
                               let uu____554 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g in
                               if uu____554
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _583 ->
                                      FStar_Pervasives_Native.Some _583)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard in
                             let lc2 =
                               let uu____586 =
                                 (FStar_All.pipe_right tlc FStar_Util.is_left)
                                   &&
                                   (FStar_TypeChecker_Util.should_return env
                                      (FStar_Pervasives_Native.Some e2) lc1) in
                               if uu____586
                               then
                                 let uu____594 =
                                   let uu____595 =
                                     FStar_TypeChecker_Util.lcomp_univ_opt
                                       lc1 in
                                   FStar_TypeChecker_Util.return_value env
                                     uu____595 t1 e2 in
                                 FStar_All.pipe_right uu____594
                                   FStar_Syntax_Util.lcomp_of_comp
                               else lc1 in
                             let uu____600 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc2 g1 in
                             match uu____600 with
                             | (lc3, g2) ->
                                 let uu____613 = set_lcomp_result lc3 t' in
                                 ((memo_tk e2 t'), uu____613, g2))))) in
           match uu____488 with | (e1, lc1, g) -> (e1, lc1, g))
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun lc ->
        let uu____651 = FStar_TypeChecker_Env.expected_typ env in
        match uu____651 with
        | FStar_Pervasives_Native.None ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____661 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____661 with
             | (e1, lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun copt ->
      fun ec ->
        let uu____714 = ec in
        match uu____714 with
        | (e, c) ->
            let tot_or_gtot c1 =
              let uu____737 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____737
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____742 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____742
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____748 =
              match copt with
              | FStar_Pervasives_Native.Some uu____761 -> (copt, c)
              | FStar_Pervasives_Native.None ->
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
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____767)) in
                  if uu____764
                  then
                    let uu____776 =
                      let uu____779 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____779 in
                    (uu____776, c)
                  else
                    (let uu____784 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____784
                     then
                       let uu____793 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____793)
                     else
                       (let uu____798 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____798
                        then
                          let uu____807 =
                            let uu____810 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____810 in
                          (uu____807, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____748 with
             | (expected_c_opt, c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____838 = FStar_Syntax_Util.lcomp_of_comp c2 in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____838 in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3 in
                      ((let uu____841 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low in
                        if uu____841
                        then
                          let uu____845 = FStar_Syntax_Print.term_to_string e in
                          let uu____847 =
                            FStar_Syntax_Print.comp_to_string c4 in
                          let uu____849 =
                            FStar_Syntax_Print.comp_to_string expected_c in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____845 uu____847 uu____849
                        else ());
                       (let uu____854 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c in
                        match uu____854 with
                        | (e1, uu____868, g) ->
                            let g1 =
                              let uu____871 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_TypeChecker_Util.label_guard uu____871
                                "could not prove post-condition" g in
                            ((let uu____874 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low in
                              if uu____874
                              then
                                let uu____877 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos in
                                let uu____879 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1 in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____877 uu____879
                              else ());
                             (let e2 =
                                FStar_TypeChecker_Util.maybe_lift env e1
                                  (FStar_Syntax_Util.comp_effect_name c4)
                                  (FStar_Syntax_Util.comp_effect_name
                                     expected_c)
                                  (FStar_Syntax_Util.comp_result c4) in
                              (e2, expected_c, g1)))))))
let no_logical_guard :
  'Auu____894 'Auu____895 .
    FStar_TypeChecker_Env.env ->
      ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t)
  =
  fun env ->
    fun uu____917 ->
      match uu____917 with
      | (te, kt, f) ->
          let uu____927 = FStar_TypeChecker_Env.guard_form f in
          (match uu____927 with
           | FStar_TypeChecker_Common.Trivial -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____935 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____941 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____935 uu____941)
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____954 = FStar_TypeChecker_Env.expected_typ env in
    match uu____954 with
    | FStar_Pervasives_Native.None ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____959 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____959
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all ->
    fun andlist ->
      fun pats ->
        let pats1 = FStar_Syntax_Util.unmeta pats in
        let uu____1001 = FStar_Syntax_Util.head_and_args pats1 in
        match uu____1001 with
        | (head1, args) ->
            let uu____1046 =
              let uu____1061 =
                let uu____1062 = FStar_Syntax_Util.un_uinst head1 in
                uu____1062.FStar_Syntax_Syntax.n in
              (uu____1061, args) in
            (match uu____1046 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1078) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1105, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1106))::(hd1,
                                                              FStar_Pervasives_Native.None)::
                (tl1, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd1 in
                 let tlvs = get_pat_vars' all andlist tl1 in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____1183, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1184))::(pat,
                                                              FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1268 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all -> fun pats -> get_pat_vars' all false pats
let check_pat_fvs :
  'Auu____1299 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1299) Prims.list -> unit
  =
  fun rng ->
    fun env ->
      fun pats ->
        fun bs ->
          let pat_vars =
            let uu____1335 = FStar_List.map FStar_Pervasives_Native.fst bs in
            let uu____1342 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats in
            get_pat_vars uu____1335 uu____1342 in
          let uu____1343 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1370 ->
                    match uu____1370 with
                    | (b, uu____1377) ->
                        let uu____1378 = FStar_Util.set_mem b pat_vars in
                        Prims.op_Negation uu____1378)) in
          match uu____1343 with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (x, uu____1385) ->
              let uu____1390 =
                let uu____1396 =
                  let uu____1398 = FStar_Syntax_Print.bv_to_string x in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1398 in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1396) in
              FStar_Errors.log_issue rng uu____1390
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en ->
    fun t ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1 in
        let uu____1424 = FStar_Syntax_Util.head_and_args t2 in
        match uu____1424 with
        | (head1, args) ->
            let uu____1469 =
              let uu____1484 =
                let uu____1485 = FStar_Syntax_Util.un_uinst head1 in
                uu____1485.FStar_Syntax_Syntax.n in
              (uu____1484, args) in
            (match uu____1469 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1501) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1523::(hd1, uu____1525)::(tl1, uu____1527)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1594 = pat_terms hd1 in
                 let uu____1597 = pat_terms tl1 in
                 FStar_List.append uu____1594 uu____1597
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____1601::(pat, uu____1603)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (subpats, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1688 -> []) in
      let rec aux t1 =
        let uu____1713 =
          let uu____1714 = FStar_Syntax_Subst.compress t1 in
          uu____1714.FStar_Syntax_Syntax.n in
        match uu____1713 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1719 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1720 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1721 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1722 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1735 -> []
        | FStar_Syntax_Syntax.Tm_unknown -> []
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
                FStar_Parser_Const.smt_theory_symbol_attr_lid in
            if uu____1846 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2, args) ->
            let uu____1879 = aux t2 in
            FStar_List.fold_left
              (fun acc ->
                 fun uu____1896 ->
                   match uu____1896 with
                   | (t3, uu____1908) ->
                       let uu____1913 = aux t3 in
                       FStar_List.append acc uu____1913) uu____1879 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1917, uu____1918) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____1960) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____1966) -> aux t2 in
      let tlist =
        let uu____1974 = FStar_All.pipe_right t pat_terms in
        FStar_All.pipe_right uu____1974 (FStar_List.collect aux) in
      if (FStar_List.length tlist) = (Prims.parse_int "0")
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s ->
                fun t1 ->
                  let uu____1997 =
                    let uu____1999 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat " " uu____1999 in
                  Prims.op_Hat s uu____1997) "" tlist in
         let uu____2003 =
           let uu____2009 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2009) in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2003)
let check_smt_pat :
  'Auu____2024 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2024) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env ->
    fun t ->
      fun bs ->
        fun c ->
          let uu____2065 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____2065
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2068;
                  FStar_Syntax_Syntax.effect_name = uu____2069;
                  FStar_Syntax_Syntax.result_typ = uu____2070;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats, uu____2074)::[];
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
  fun env ->
    fun actuals ->
      fun expected_c ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___345_2200 = env in
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
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____2226 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____2226
               then
                 let uu____2229 =
                   FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____2232 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2229 uu____2232
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2266 ->
                         match uu____2266 with
                         | (b, uu____2276) ->
                             let t =
                               let uu____2282 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2282 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2285 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2286 -> []
                              | uu____2301 ->
                                  let uu____2302 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____2302]))) in
               let as_lex_list dec =
                 let uu____2315 = FStar_Syntax_Util.head_and_args dec in
                 match uu____2315 with
                 | (head1, uu____2335) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2363 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____2371 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2380 ->
                         match uu___1_2380 with
                         | FStar_Syntax_Syntax.DECREASES uu____2382 -> true
                         | uu____2386 -> false)) in
               match uu____2371 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2393 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   (match xs with | x::[] -> x | uu____2414 -> mk_lex_list xs)) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____2443 =
              match uu____2443 with
              | (l, t, u_names) ->
                  let uu____2467 =
                    let uu____2468 = FStar_Syntax_Subst.compress t in
                    uu____2468.FStar_Syntax_Syntax.n in
                  (match uu____2467 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2527 ->
                                 match uu____2527 with
                                 | (x, imp) ->
                                     let uu____2546 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____2546
                                     then
                                       let uu____2555 =
                                         let uu____2556 =
                                           let uu____2559 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____2559 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2556
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____2555, imp)
                                     else (x, imp))) in
                       let uu____2566 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____2566 with
                        | (formals2, c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____2587 =
                                let uu____2592 =
                                  let uu____2593 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____2602 =
                                    let uu____2613 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____2613] in
                                  uu____2593 :: uu____2602 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2592 in
                              uu____2587 FStar_Pervasives_Native.None r in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1 in
                            let uu____2648 = FStar_Util.prefix formals2 in
                            (match uu____2648 with
                             | (bs, (last1, imp)) ->
                                 let last2 =
                                   let uu___412_2711 = last1 in
                                   let uu____2712 =
                                     FStar_Syntax_Util.refine last1 precedes2 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___412_2711.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___412_2711.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2712
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____2748 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____2748
                                   then
                                     let uu____2751 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____2753 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____2755 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2751 uu____2753 uu____2755
                                   else ());
                                  (l, t', u_names))))
                   | uu____2762 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos) in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt ->
    fun g ->
      match topt with
      | FStar_Pervasives_Native.None -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1 ->
               let uu____2826 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1 in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2826)
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____3439 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
       if uu____3439
       then
         let uu____3442 =
           let uu____3444 = FStar_TypeChecker_Env.get_range env in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3444 in
         let uu____3446 = FStar_Syntax_Print.term_to_string e in
         let uu____3448 =
           let uu____3450 = FStar_Syntax_Subst.compress e in
           FStar_Syntax_Print.tag_of_term uu____3450 in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3442
           uu____3446 uu____3448
       else ());
      (let uu____3454 =
         FStar_Util.record_time
           (fun uu____3473 ->
              tc_maybe_toplevel_term
                (let uu___431_3476 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___431_3476.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___431_3476.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___431_3476.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___431_3476.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___431_3476.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___431_3476.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___431_3476.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___431_3476.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___431_3476.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___431_3476.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___431_3476.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___431_3476.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___431_3476.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___431_3476.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___431_3476.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___431_3476.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___431_3476.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___431_3476.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___431_3476.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___431_3476.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___431_3476.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___431_3476.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___431_3476.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___431_3476.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___431_3476.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___431_3476.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___431_3476.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___431_3476.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___431_3476.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___431_3476.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___431_3476.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___431_3476.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___431_3476.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___431_3476.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___431_3476.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___431_3476.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___431_3476.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___431_3476.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___431_3476.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___431_3476.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___431_3476.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___431_3476.FStar_TypeChecker_Env.nbe)
                 }) e) in
       match uu____3454 with
       | (r, ms) ->
           ((let uu____3501 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____3501
             then
               ((let uu____3505 =
                   let uu____3507 = FStar_TypeChecker_Env.get_range env in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3507 in
                 let uu____3509 = FStar_Syntax_Print.term_to_string e in
                 let uu____3511 =
                   let uu____3513 = FStar_Syntax_Subst.compress e in
                   FStar_Syntax_Print.tag_of_term uu____3513 in
                 let uu____3514 = FStar_Util.string_of_int ms in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3505 uu____3509 uu____3511 uu____3514);
                (let uu____3517 = r in
                 match uu____3517 with
                 | (e1, uu____3525, uu____3526) ->
                     let uu____3527 =
                       let uu____3529 = FStar_TypeChecker_Env.get_range env in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3529 in
                     let uu____3531 = FStar_Syntax_Print.term_to_string e1 in
                     let uu____3533 =
                       let uu____3535 = FStar_Syntax_Subst.compress e1 in
                       FStar_Syntax_Print.tag_of_term uu____3535 in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3527
                       uu____3531 uu____3533))
             else ());
            r))
and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      (let uu____3553 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
       if uu____3553
       then
         let uu____3556 =
           let uu____3558 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3558 in
         let uu____3560 = FStar_Syntax_Print.tag_of_term top in
         let uu____3562 = FStar_Syntax_Print.term_to_string top in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3556 uu____3560
           uu____3562
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3573 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3603 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3610 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3623 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3624 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3625 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3626 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3627 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3646 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3661 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3668 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
           let projl uu___2_3684 =
             match uu___2_3684 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3690 -> failwith "projl fail" in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3706 =
                 let uu____3707 = FStar_Syntax_Subst.compress t in
                 uu____3707.FStar_Syntax_Syntax.n in
               match uu____3706 with
               | FStar_Syntax_Syntax.Tm_name uu____3711 -> true
               | uu____3713 -> false in
             FStar_Util.for_some
               (fun uu____3723 ->
                  match uu____3723 with
                  | (uu____3729, t) ->
                      let uu____3731 = is_name1 t in
                      Prims.op_Negation uu____3731)
               qi1.FStar_Syntax_Syntax.antiquotes in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static when non_trivial_antiquotes qi
                ->
                let e0 = e in
                let newbvs =
                  FStar_List.map
                    (fun uu____3750 ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs in
                let lbs =
                  FStar_List.map
                    (fun uu____3793 ->
                       match uu____3793 with
                       | ((bv, t), bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z in
                let qi1 =
                  let uu___504_3822 = qi in
                  let uu____3823 =
                    FStar_List.map
                      (fun uu____3851 ->
                         match uu____3851 with
                         | ((bv, uu____3867), bv') ->
                             let uu____3879 =
                               FStar_Syntax_Syntax.bv_to_name bv' in
                             (bv, uu____3879)) z in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___504_3822.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3823
                  } in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                let e1 =
                  FStar_List.fold_left
                    (fun t ->
                       fun lb ->
                         let uu____3891 =
                           let uu____3898 =
                             let uu____3899 =
                               let uu____3913 =
                                 let uu____3916 =
                                   let uu____3917 =
                                     let uu____3924 =
                                       projl lb.FStar_Syntax_Syntax.lbname in
                                     FStar_Syntax_Syntax.mk_binder uu____3924 in
                                   [uu____3917] in
                                 FStar_Syntax_Subst.close uu____3916 t in
                               ((false, [lb]), uu____3913) in
                             FStar_Syntax_Syntax.Tm_let uu____3899 in
                           FStar_Syntax_Syntax.mk uu____3898 in
                         uu____3891 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term in
                let uu____3960 =
                  FStar_List.fold_right
                    (fun uu____3996 ->
                       fun uu____3997 ->
                         match (uu____3996, uu____3997) with
                         | ((bv, tm), (aqs_rev, guard)) ->
                             let uu____4066 = tc_term env_tm tm in
                             (match uu____4066 with
                              | (tm1, uu____4084, g) ->
                                  let uu____4086 =
                                    FStar_TypeChecker_Env.conj_guard g guard in
                                  (((bv, tm1) :: aqs_rev), uu____4086))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard) in
                (match uu____3960 with
                 | (aqs_rev, guard) ->
                     let qi1 =
                       let uu___532_4128 = qi in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___532_4128.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       } in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic ->
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
                    } in
                let uu____4147 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____4147 with
                 | (env', uu____4161) ->
                     let uu____4166 =
                       tc_term
                         (let uu___541_4175 = env' in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___541_4175.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___541_4175.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___541_4175.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___541_4175.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___541_4175.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___541_4175.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___541_4175.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___541_4175.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___541_4175.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___541_4175.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___541_4175.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___541_4175.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___541_4175.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___541_4175.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___541_4175.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___541_4175.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___541_4175.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___541_4175.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___541_4175.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___541_4175.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___541_4175.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___541_4175.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___541_4175.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___541_4175.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___541_4175.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___541_4175.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___541_4175.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___541_4175.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___541_4175.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___541_4175.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___541_4175.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___541_4175.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___541_4175.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___541_4175.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___541_4175.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___541_4175.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___541_4175.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___541_4175.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___541_4175.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___541_4175.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___541_4175.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___541_4175.FStar_TypeChecker_Env.nbe)
                          }) qt in
                     (match uu____4166 with
                      | (qt1, uu____4184, uu____4185) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4191 =
                            let uu____4198 =
                              let uu____4203 =
                                FStar_Syntax_Util.lcomp_of_comp c in
                              FStar_Util.Inr uu____4203 in
                            value_check_expected_typ env1 top uu____4198
                              FStar_TypeChecker_Env.trivial_guard in
                          (match uu____4191 with
                           | (t1, lc, g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   FStar_Pervasives_Native.None
                                   t1.FStar_Syntax_Syntax.pos in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4220;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4221;
             FStar_Syntax_Syntax.ltyp = uu____4222;
             FStar_Syntax_Syntax.rng = uu____4223;_}
           ->
           let uu____4234 = FStar_Syntax_Util.unlazy top in
           tc_term env1 uu____4234
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat))
           ->
           let uu____4241 = tc_tot_or_gtot_term env1 e1 in
           (match uu____4241 with
            | (e2, c, g) ->
                let g1 =
                  let uu___571_4258 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___571_4258.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___571_4258.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___571_4258.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____4259 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____4259, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____4280 = FStar_Syntax_Util.type_u () in
           (match uu____4280 with
            | (t, u) ->
                let uu____4293 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____4293 with
                 | (e2, c, g) ->
                     let uu____4309 =
                       let uu____4326 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____4326 with
                       | (env2, uu____4350) -> tc_smt_pats env2 pats in
                     (match uu____4309 with
                      | (pats1, g') ->
                          let g'1 =
                            let uu___592_4388 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___592_4388.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___592_4388.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___592_4388.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____4389 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4392 =
                            FStar_TypeChecker_Env.conj_guard g g'1 in
                          (uu____4389, c, uu____4392))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence))
           ->
           let uu____4398 =
             let uu____4399 = FStar_Syntax_Subst.compress e1 in
             uu____4399.FStar_Syntax_Syntax.n in
           (match uu____4398 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4408,
                  { FStar_Syntax_Syntax.lbname = x;
                    FStar_Syntax_Syntax.lbunivs = uu____4410;
                    FStar_Syntax_Syntax.lbtyp = uu____4411;
                    FStar_Syntax_Syntax.lbeff = uu____4412;
                    FStar_Syntax_Syntax.lbdef = e11;
                    FStar_Syntax_Syntax.lbattrs = uu____4414;
                    FStar_Syntax_Syntax.lbpos = uu____4415;_}::[]),
                 e2)
                ->
                let uu____4446 =
                  let uu____4453 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____4453 e11 in
                (match uu____4446 with
                 | (e12, c1, g1) ->
                     let uu____4463 = tc_term env1 e2 in
                     (match uu____4463 with
                      | (e21, c2, g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2) in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ in
                          let attrs =
                            let uu____4487 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_Syntax_Syntax.eff_name in
                            if uu____4487
                            then [FStar_Syntax_Util.inline_let_attr]
                            else [] in
                          let e3 =
                            let uu____4497 =
                              let uu____4504 =
                                let uu____4505 =
                                  let uu____4519 =
                                    let uu____4527 =
                                      let uu____4530 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos)) in
                                      [uu____4530] in
                                    (false, uu____4527) in
                                  (uu____4519, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____4505 in
                              FStar_Syntax_Syntax.mk uu____4504 in
                            uu____4497 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____4554 =
                            FStar_TypeChecker_Env.conj_guard g1 g2 in
                          (e5, c, uu____4554)))
            | uu____4555 ->
                let uu____4556 = tc_term env1 e1 in
                (match uu____4556 with
                 | (e2, c, g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic uu____4578) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic_lift uu____4590) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
           let uu____4609 = tc_term env1 e1 in
           (match uu____4609 with
            | (e2, c, g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inr expected_c, topt), uu____4633) ->
           let uu____4680 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4680 with
            | (env0, uu____4694) ->
                let uu____4699 = tc_comp env0 expected_c in
                (match uu____4699 with
                 | (expected_c1, uu____4713, g) ->
                     let uu____4715 =
                       let uu____4722 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0) in
                       tc_term uu____4722 e1 in
                     (match uu____4715 with
                      | (e2, c', g') ->
                          let uu____4732 =
                            let uu____4739 =
                              let uu____4744 =
                                FStar_Syntax_Syntax.lcomp_comp c' in
                              (e2, uu____4744) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____4739 in
                          (match uu____4732 with
                           | (e3, expected_c2, g'') ->
                               let uu____4754 = tc_tactic_opt env0 topt in
                               (match uu____4754 with
                                | (topt1, gtac) ->
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
                                        top.FStar_Syntax_Syntax.pos in
                                    let lc =
                                      FStar_Syntax_Util.lcomp_of_comp
                                        expected_c2 in
                                    let f =
                                      let uu____4814 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g'' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____4814 in
                                    let uu____4815 =
                                      comp_check_expected_typ env1 e4 lc in
                                    (match uu____4815 with
                                     | (e5, c, f2) ->
                                         let final_guard =
                                           let uu____4832 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2 in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____4832 in
                                         let uu____4833 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac in
                                         (e5, c, uu____4833)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inl t, topt), uu____4837) ->
           let uu____4884 = FStar_Syntax_Util.type_u () in
           (match uu____4884 with
            | (k, u) ->
                let uu____4897 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____4897 with
                 | (t1, uu____4911, f) ->
                     let uu____4913 = tc_tactic_opt env1 topt in
                     (match uu____4913 with
                      | (topt1, gtac) ->
                          let uu____4932 =
                            let uu____4939 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                            tc_term uu____4939 e1 in
                          (match uu____4932 with
                           | (e2, c, g) ->
                               let uu____4949 =
                                 let uu____4954 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____4960 ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____4954 e2 c f in
                               (match uu____4949 with
                                | (c1, f1) ->
                                    let uu____4970 =
                                      let uu____4977 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos in
                                      comp_check_expected_typ env1 uu____4977
                                        c1 in
                                    (match uu____4970 with
                                     | (e3, c2, f2) ->
                                         let final_guard =
                                           let uu____5024 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2 in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5024 in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard in
                                         let uu____5026 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac in
                                         (e3, c2, uu____5026)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____5027;
              FStar_Syntax_Syntax.vars = uu____5028;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____5107 = FStar_Syntax_Util.head_and_args top in
           (match uu____5107 with
            | (unary_op1, uu____5131) ->
                let head1 =
                  let uu____5159 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5159 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____5207;
              FStar_Syntax_Syntax.vars = uu____5208;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____5287 = FStar_Syntax_Util.head_and_args top in
           (match uu____5287 with
            | (unary_op1, uu____5311) ->
                let head1 =
                  let uu____5339 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5339 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5387);
              FStar_Syntax_Syntax.pos = uu____5388;
              FStar_Syntax_Syntax.vars = uu____5389;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____5468 = FStar_Syntax_Util.head_and_args top in
           (match uu____5468 with
            | (unary_op1, uu____5492) ->
                let head1 =
                  let uu____5520 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5520 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____5568;
              FStar_Syntax_Syntax.vars = uu____5569;_},
            a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____5665 = FStar_Syntax_Util.head_and_args top in
           (match uu____5665 with
            | (unary_op1, uu____5689) ->
                let head1 =
                  let uu____5717 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5717 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____5773;
              FStar_Syntax_Syntax.vars = uu____5774;_},
            (e1, FStar_Pervasives_Native.None)::[])
           ->
           let uu____5812 =
             let uu____5819 =
               let uu____5820 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5820 in
             tc_term uu____5819 e1 in
           (match uu____5812 with
            | (e2, c, g) ->
                let uu____5844 = FStar_Syntax_Util.head_and_args top in
                (match uu____5844 with
                 | (head1, uu____5868) ->
                     let uu____5893 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____5926 =
                       let uu____5927 =
                         let uu____5928 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____5928 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5927 in
                     (uu____5893, uu____5926, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____5929;
              FStar_Syntax_Syntax.vars = uu____5930;_},
            (t, FStar_Pervasives_Native.None)::(r,
                                                FStar_Pervasives_Native.None)::[])
           ->
           let uu____5983 = FStar_Syntax_Util.head_and_args top in
           (match uu____5983 with
            | (head1, uu____6007) ->
                let env' =
                  let uu____6033 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6033 in
                let uu____6034 = tc_term env' r in
                (match uu____6034 with
                 | (er, uu____6048, gr) ->
                     let uu____6050 = tc_term env1 t in
                     (match uu____6050 with
                      | (t1, tt, gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1 in
                          let uu____6067 =
                            let uu____6068 =
                              let uu____6073 =
                                let uu____6074 =
                                  FStar_Syntax_Syntax.as_arg t1 in
                                let uu____6083 =
                                  let uu____6094 =
                                    FStar_Syntax_Syntax.as_arg r in
                                  [uu____6094] in
                                uu____6074 :: uu____6083 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6073 in
                            uu____6068 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____6067, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6127;
              FStar_Syntax_Syntax.vars = uu____6128;_},
            uu____6129)
           ->
           let uu____6154 =
             let uu____6160 =
               let uu____6162 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____6162 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6160) in
           FStar_Errors.raise_error uu____6154 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6172;
              FStar_Syntax_Syntax.vars = uu____6173;_},
            uu____6174)
           ->
           let uu____6199 =
             let uu____6205 =
               let uu____6207 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____6207 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6205) in
           FStar_Errors.raise_error uu____6199 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____6217;
              FStar_Syntax_Syntax.vars = uu____6218;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6265 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____6265 with
             | (env0, uu____6279) ->
                 let uu____6284 = tc_term env0 e1 in
                 (match uu____6284 with
                  | (e2, c, g) ->
                      let uu____6300 = FStar_Syntax_Util.head_and_args top in
                      (match uu____6300 with
                       | (reify_op, uu____6324) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_Syntax_Syntax.res_typ in
                           let ef =
                             let uu____6351 =
                               FStar_Syntax_Syntax.lcomp_comp c in
                             FStar_Syntax_Util.comp_effect_name uu____6351 in
                           ((let uu____6355 =
                               let uu____6357 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef in
                               Prims.op_Negation uu____6357 in
                             if uu____6355
                             then
                               let uu____6360 =
                                 let uu____6366 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____6366) in
                               FStar_Errors.raise_error uu____6360
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____6373 =
                                 FStar_Syntax_Syntax.lcomp_comp c in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____6373 u_c in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos in
                             let c1 =
                               let uu____6410 =
                                 FStar_TypeChecker_Env.is_total_effect env1
                                   ef in
                               if uu____6410
                               then
                                 let uu____6413 =
                                   FStar_Syntax_Syntax.mk_Total repr in
                                 FStar_All.pipe_right uu____6413
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
                                    } in
                                  let uu____6425 =
                                    FStar_Syntax_Syntax.mk_Comp ct in
                                  FStar_All.pipe_right uu____6425
                                    FStar_Syntax_Util.lcomp_of_comp) in
                             let uu____6426 =
                               comp_check_expected_typ env1 e3 c1 in
                             match uu____6426 with
                             | (e4, c2, g') ->
                                 let uu____6442 =
                                   FStar_TypeChecker_Env.conj_guard g g' in
                                 (e4, c2, uu____6442)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6444;
              FStar_Syntax_Syntax.vars = uu____6445;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6493 =
               let uu____6495 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l in
               Prims.op_Negation uu____6495 in
             if uu____6493
             then
               let uu____6498 =
                 let uu____6504 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6504) in
               FStar_Errors.raise_error uu____6498 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6510 = FStar_Syntax_Util.head_and_args top in
             match uu____6510 with
             | (reflect_op, uu____6534) ->
                 let uu____6559 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____6559 with
                  | FStar_Pervasives_Native.None ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____6599 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____6599 with
                       | (env_no_ex, topt) ->
                           let uu____6618 =
                             let u = FStar_TypeChecker_Env.new_u_univ () in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             let t =
                               let uu____6638 =
                                 let uu____6645 =
                                   let uu____6646 =
                                     let uu____6663 =
                                       let uu____6674 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun in
                                       let uu____6683 =
                                         let uu____6694 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         [uu____6694] in
                                       uu____6674 :: uu____6683 in
                                     (repr, uu____6663) in
                                   FStar_Syntax_Syntax.Tm_app uu____6646 in
                                 FStar_Syntax_Syntax.mk uu____6645 in
                               uu____6638 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6739 =
                               let uu____6746 =
                                 let uu____6747 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1 in
                                 FStar_All.pipe_right uu____6747
                                   FStar_Pervasives_Native.fst in
                               tc_tot_or_gtot_term uu____6746 t in
                             match uu____6739 with
                             | (t1, uu____6773, g) ->
                                 let uu____6775 =
                                   let uu____6776 =
                                     FStar_Syntax_Subst.compress t1 in
                                   uu____6776.FStar_Syntax_Syntax.n in
                                 (match uu____6775 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____6789,
                                       (res, uu____6791)::(wp, uu____6793)::[])
                                      -> (t1, res, wp, g)
                                  | uu____6850 -> failwith "Impossible") in
                           (match uu____6618 with
                            | (expected_repr_typ, res_typ, wp, g0) ->
                                let uu____6876 =
                                  let uu____6883 =
                                    tc_tot_or_gtot_term env_no_ex e1 in
                                  match uu____6883 with
                                  | (e2, c, g) ->
                                      ((let uu____6900 =
                                          let uu____6902 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____6902 in
                                        if uu____6900
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____6925 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ in
                                        match uu____6925 with
                                        | FStar_Pervasives_Native.None ->
                                            ((let uu____6936 =
                                                let uu____6946 =
                                                  let uu____6954 =
                                                    let uu____6956 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr in
                                                    let uu____6958 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____6956 uu____6958 in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____6954,
                                                    (e2.FStar_Syntax_Syntax.pos)) in
                                                [uu____6946] in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____6936);
                                             (let uu____6976 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0 in
                                              (e2, uu____6976)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____6980 =
                                              let uu____6981 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____6981 in
                                            (e2, uu____6980))) in
                                (match uu____6876 with
                                 | (e2, g) ->
                                     let c =
                                       let uu____6997 =
                                         let uu____6998 =
                                           let uu____6999 =
                                             let uu____7000 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ in
                                             [uu____7000] in
                                           let uu____7001 =
                                             let uu____7012 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____7012] in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____6999;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7001;
                                             FStar_Syntax_Syntax.flags = []
                                           } in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____6998 in
                                       FStar_All.pipe_right uu____6997
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____7072 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____7072 with
                                      | (e4, c1, g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_Syntax_Syntax.eff_name),
                                                        (c1.FStar_Syntax_Syntax.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos in
                                          let uu____7095 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g in
                                          (e5, c1, uu____7095))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7134 = FStar_Syntax_Util.head_and_args top in
           (match uu____7134 with
            | (head2, args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,
            (uu____7184, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____7185))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7238 = FStar_Syntax_Util.head_and_args top in
           (match uu____7238 with
            | (head2, args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7313 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7523 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____7313 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1, args) ->
           let env0 = env1 in
           let env2 =
             let uu____7642 =
               let uu____7643 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____7643 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____7642 instantiate_both in
           ((let uu____7659 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____7659
             then
               let uu____7662 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____7664 = FStar_Syntax_Print.term_to_string top in
               let uu____7666 =
                 let uu____7668 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____7668
                   (fun uu___3_7675 ->
                      match uu___3_7675 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7662
                 uu____7664 uu____7666
             else ());
            (let uu____7684 = tc_term (no_inst env2) head1 in
             match uu____7684 with
             | (head2, chead, g_head) ->
                 let uu____7700 =
                   let uu____7707 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____7710 = FStar_Options.lax () in
                         Prims.op_Negation uu____7710))
                       && (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____7707
                   then
                     let uu____7719 =
                       let uu____7726 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____7726 in
                     match uu____7719 with | (e1, c, g) -> (e1, c, g)
                   else
                     (let uu____7740 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____7740) in
                 (match uu____7700 with
                  | (e1, c, g) ->
                      let uu____7752 =
                        let uu____7759 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
                        if uu____7759
                        then
                          let uu____7768 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ in
                          match uu____7768 with
                          | (e2, res_typ, implicits) ->
                              let uu____7784 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ in
                              (e2, uu____7784, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                      (match uu____7752 with
                       | (e2, c1, implicits) ->
                           ((let uu____7797 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme in
                             if uu____7797
                             then
                               let uu____7800 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____7800
                             else ());
                            (let uu____7805 =
                               comp_check_expected_typ env0 e2 c1 in
                             match uu____7805 with
                             | (e3, c2, g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g' in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits in
                                 ((let uu____7824 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme in
                                   if uu____7824
                                   then
                                     let uu____7827 =
                                       FStar_Syntax_Print.term_to_string e3 in
                                     let uu____7829 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1 in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____7827 uu____7829
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
           let uu____7872 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____7872 with
            | (env11, topt) ->
                let env12 = instantiate_both env11 in
                let uu____7892 = tc_term env12 e1 in
                (match uu____7892 with
                 | (e11, c1, g1) ->
                     let uu____7908 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None ->
                           let uu____7922 = FStar_Syntax_Util.type_u () in
                           (match uu____7922 with
                            | (k, uu____7934) ->
                                let uu____7935 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k in
                                (match uu____7935 with
                                 | (res_t, uu____7956, g) ->
                                     let uu____7970 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t in
                                     let uu____7971 =
                                       FStar_TypeChecker_Env.conj_guard g1 g in
                                     (uu____7970, res_t, uu____7971))) in
                     (match uu____7908 with
                      | (env_branches, res_t, g11) ->
                          ((let uu____7982 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____7982
                            then
                              let uu____7985 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____7985
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____8112 =
                              let uu____8117 =
                                FStar_List.fold_right
                                  (fun uu____8199 ->
                                     fun uu____8200 ->
                                       match (uu____8199, uu____8200) with
                                       | ((branch1, f, eff_label, cflags, c,
                                           g),
                                          (caccum, gaccum)) ->
                                           let uu____8445 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8445)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard) in
                              match uu____8117 with
                              | (cases, g) ->
                                  let uu____8550 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____8550, g) in
                            match uu____8112 with
                            | (c_branches, g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches) in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____8692 ->
                                              match uu____8692 with
                                              | ((pat, wopt, br), uu____8737,
                                                 eff_label, uu____8739,
                                                 uu____8740, uu____8741) ->
                                                  let uu____8778 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t in
                                                  (pat, wopt, uu____8778))) in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos in
                                  let uu____8845 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____8845
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____8853 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____8853 in
                                     let lb =
                                       let uu____8857 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____8857 e11 []
                                         e11.FStar_Syntax_Syntax.pos in
                                     let e2 =
                                       let uu____8863 =
                                         let uu____8870 =
                                           let uu____8871 =
                                             let uu____8885 =
                                               let uu____8888 =
                                                 let uu____8889 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____8889] in
                                               FStar_Syntax_Subst.close
                                                 uu____8888 e_match in
                                             ((false, [lb]), uu____8885) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____8871 in
                                         FStar_Syntax_Syntax.mk uu____8870 in
                                       uu____8863
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____8922 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____8922
                                  then
                                    let uu____8925 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____8927 =
                                      FStar_Syntax_Print.lcomp_to_string cres in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____8925 uu____8927
                                  else ());
                                 (let uu____8932 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches in
                                  (e2, cres, uu____8932))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8933;
               FStar_Syntax_Syntax.lbunivs = uu____8934;
               FStar_Syntax_Syntax.lbtyp = uu____8935;
               FStar_Syntax_Syntax.lbeff = uu____8936;
               FStar_Syntax_Syntax.lbdef = uu____8937;
               FStar_Syntax_Syntax.lbattrs = uu____8938;
               FStar_Syntax_Syntax.lbpos = uu____8939;_}::[]),
            uu____8940)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8966), uu____8967) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8985;
               FStar_Syntax_Syntax.lbunivs = uu____8986;
               FStar_Syntax_Syntax.lbtyp = uu____8987;
               FStar_Syntax_Syntax.lbeff = uu____8988;
               FStar_Syntax_Syntax.lbdef = uu____8989;
               FStar_Syntax_Syntax.lbattrs = uu____8990;
               FStar_Syntax_Syntax.lbpos = uu____8991;_}::uu____8992),
            uu____8993)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____9021), uu____9022) ->
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
  fun head1 ->
    fun env ->
      fun args ->
        fun rng ->
          let uu____9056 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9095))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9136 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____9056 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____9169 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____9169 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____9173 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9173) in
              let uu____9176 =
                let uu____9183 =
                  let uu____9184 =
                    let uu____9185 = FStar_Syntax_Util.type_u () in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9185 in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9184 in
                tc_term uu____9183 typ in
              (match uu____9176 with
               | (typ1, uu____9201, g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9204 = tc_tactic env tau in
                     match uu____9204 with
                     | (tau1, uu____9218, g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1189_9223 = tau1 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1189_9223.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1189_9223.FStar_Syntax_Syntax.vars)
                                }) in
                           (let uu____9225 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac") in
                            if uu____9225
                            then
                              let uu____9230 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print1 "Got %s\n" uu____9230
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9236 =
                              let uu____9237 =
                                FStar_Syntax_Syntax.mk_Total typ1 in
                              FStar_All.pipe_left
                                FStar_Syntax_Util.lcomp_of_comp uu____9237 in
                            (t, uu____9236,
                              FStar_TypeChecker_Env.trivial_guard)))))))
and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun tau ->
      let env1 =
        let uu___1197_9241 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1197_9241.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1197_9241.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1197_9241.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1197_9241.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1197_9241.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1197_9241.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1197_9241.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1197_9241.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1197_9241.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1197_9241.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1197_9241.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1197_9241.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1197_9241.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1197_9241.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1197_9241.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1197_9241.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1197_9241.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1197_9241.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1197_9241.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1197_9241.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1197_9241.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1197_9241.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1197_9241.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1197_9241.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1197_9241.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1197_9241.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1197_9241.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1197_9241.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1197_9241.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1197_9241.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1197_9241.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1197_9241.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1197_9241.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1197_9241.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1197_9241.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1197_9241.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1197_9241.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1197_9241.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1197_9241.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1197_9241.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1197_9241.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1197_9241.FStar_TypeChecker_Env.nbe)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit
and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun topt ->
      match topt with
      | FStar_Pervasives_Native.None ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____9264 = tc_tactic env tactic in
          (match uu____9264 with
           | (tactic1, uu____9278, g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))
and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____9330 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0 in
        match uu____9330 with
        | (e2, t, implicits) ->
            let tc =
              let uu____9351 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____9351
              then FStar_Util.Inl t
              else
                (let uu____9360 =
                   let uu____9361 = FStar_Syntax_Syntax.mk_Total t in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____9361 in
                 FStar_Util.Inr uu____9360) in
            let is_data_ctor uu___4_9370 =
              match uu___4_9370 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9375) -> true
              | uu____9383 -> false in
            let uu____9387 =
              (is_data_ctor dc) &&
                (let uu____9390 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____9390) in
            if uu____9387
            then
              let uu____9399 =
                let uu____9405 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9405) in
              let uu____9409 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____9399 uu____9409
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9427 =
            let uu____9429 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9429 in
          failwith uu____9427
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____9456 =
            let uu____9461 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____9461 in
          value_check_expected_typ env1 e uu____9456
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____9463 =
            let uu____9476 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____9476 with
            | FStar_Pervasives_Native.None ->
                let uu____9491 = FStar_Syntax_Util.type_u () in
                (match uu____9491 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____9463 with
           | (t, uu____9529, g0) ->
               let uu____9543 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____9543 with
                | (e1, uu____9564, g1) ->
                    let uu____9578 =
                      let uu____9579 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____9579
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____9580 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____9578, uu____9580)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9582 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9592 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____9592)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____9582 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1262_9606 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1262_9606.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1262_9606.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____9609 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____9609 with
                 | (e2, t1, implicits) ->
                     let tc =
                       let uu____9630 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____9630
                       then FStar_Util.Inl t1
                       else
                         (let uu____9639 =
                            let uu____9640 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____9640 in
                          FStar_Util.Inr uu____9639) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9642;
             FStar_Syntax_Syntax.vars = uu____9643;_},
           uu____9644)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9649 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9649
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9659 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9659
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9669;
             FStar_Syntax_Syntax.vars = uu____9670;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____9679 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____9679 with
           | ((us', t), range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9703 =
                     let uu____9709 =
                       let uu____9711 = FStar_Syntax_Print.fv_to_string fv in
                       let uu____9713 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____9715 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9711 uu____9713 uu____9715 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9709) in
                   let uu____9719 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____9703 uu____9719)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9736 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9741 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9741 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9743 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____9743 with
           | ((us, t), range) ->
               ((let uu____9766 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____9766
                 then
                   let uu____9771 =
                     let uu____9773 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____9773 in
                   let uu____9774 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____9776 = FStar_Range.string_of_range range in
                   let uu____9778 = FStar_Range.string_of_use_range range in
                   let uu____9780 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____9771 uu____9774 uu____9776 uu____9778 uu____9780
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9788 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9788 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____9816 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____9816 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____9830 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9830 with
                | (env2, uu____9844) ->
                    let uu____9849 = tc_binders env2 bs1 in
                    (match uu____9849 with
                     | (bs2, env3, g, us) ->
                         let uu____9868 = tc_comp env3 c1 in
                         (match uu____9868 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___1342_9887 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1342_9887.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1342_9887.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____9898 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____9898 in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 bs2 g1 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____9914 =
            let uu____9919 =
              let uu____9920 = FStar_Syntax_Syntax.mk_binder x in
              [uu____9920] in
            FStar_Syntax_Subst.open_term uu____9919 phi in
          (match uu____9914 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____9948 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9948 with
                | (env2, uu____9962) ->
                    let uu____9967 =
                      let uu____9982 = FStar_List.hd x1 in
                      tc_binder env2 uu____9982 in
                    (match uu____9967 with
                     | (x2, env3, f1, u) ->
                         ((let uu____10018 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____10018
                           then
                             let uu____10021 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____10023 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____10025 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10021 uu____10023 uu____10025
                           else ());
                          (let uu____10032 = FStar_Syntax_Util.type_u () in
                           match uu____10032 with
                           | (t_phi, uu____10044) ->
                               let uu____10045 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____10045 with
                                | (phi2, uu____10059, f2) ->
                                    let e1 =
                                      let uu___1380_10064 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1380_10064.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1380_10064.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____10073 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10073 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____10101) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____10128 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium in
            if uu____10128
            then
              let uu____10131 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1393_10135 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1393_10135.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1393_10135.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10131
            else ());
           (let uu____10151 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____10151 with
            | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____10164 ->
          let uu____10165 =
            let uu____10167 = FStar_Syntax_Print.term_to_string top in
            let uu____10169 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10167
              uu____10169 in
          failwith uu____10165
and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun r ->
      fun c ->
        match c with
        | FStar_Const.Const_unit -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10181 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10183, FStar_Pervasives_Native.None)
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10196, FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed, FStar_Const.Int8) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed, FStar_Const.Int16) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed, FStar_Const.Int32) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed, FStar_Const.Int64) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned, FStar_Const.Int8) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned, FStar_Const.Int16) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned, FStar_Const.Int32) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned, FStar_Const.Int64) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____10214 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10220 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10222 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10223 ->
            let uu____10225 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
            FStar_All.pipe_right uu____10225 FStar_Util.must
        | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10230 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of ->
            let uu____10231 =
              let uu____10237 =
                let uu____10239 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10239 in
              (FStar_Errors.Fatal_IllTyped, uu____10237) in
            FStar_Errors.raise_error uu____10231 r
        | FStar_Const.Const_set_range_of ->
            let uu____10243 =
              let uu____10249 =
                let uu____10251 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10251 in
              (FStar_Errors.Fatal_IllTyped, uu____10249) in
            FStar_Errors.raise_error uu____10243 r
        | FStar_Const.Const_reify ->
            let uu____10255 =
              let uu____10261 =
                let uu____10263 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10263 in
              (FStar_Errors.Fatal_IllTyped, uu____10261) in
            FStar_Errors.raise_error uu____10255 r
        | FStar_Const.Const_reflect uu____10267 ->
            let uu____10268 =
              let uu____10274 =
                let uu____10276 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10276 in
              (FStar_Errors.Fatal_IllTyped, uu____10274) in
            FStar_Errors.raise_error uu____10268 r
        | uu____10280 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r
and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun c ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uu____10299) ->
          let uu____10308 = FStar_Syntax_Util.type_u () in
          (match uu____10308 with
           | (k, u) ->
               let uu____10321 = tc_check_tot_or_gtot_term env t k in
               (match uu____10321 with
                | (t1, uu____10335, g) ->
                    let uu____10337 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____10337, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____10339) ->
          let uu____10348 = FStar_Syntax_Util.type_u () in
          (match uu____10348 with
           | (k, u) ->
               let uu____10361 = tc_check_tot_or_gtot_term env t k in
               (match uu____10361 with
                | (t1, uu____10375, g) ->
                    let uu____10377 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____10377, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____10387 =
              let uu____10392 =
                let uu____10393 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____10393 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10392 in
            uu____10387 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____10410 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____10410 with
           | (tc1, uu____10424, f) ->
               let uu____10426 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____10426 with
                | (head3, args) ->
                    let comp_univs =
                      let uu____10476 =
                        let uu____10477 = FStar_Syntax_Subst.compress head3 in
                        uu____10477.FStar_Syntax_Syntax.n in
                      match uu____10476 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10480, us) -> us
                      | uu____10486 -> [] in
                    let uu____10487 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____10487 with
                     | (uu____10510, args1) ->
                         let uu____10536 =
                           let uu____10559 = FStar_List.hd args1 in
                           let uu____10576 = FStar_List.tl args1 in
                           (uu____10559, uu____10576) in
                         (match uu____10536 with
                          | (res, args2) ->
                              let uu____10657 =
                                let uu____10666 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10694 ->
                                          match uu___5_10694 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10702 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____10702 with
                                               | (env1, uu____10714) ->
                                                   let uu____10719 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____10719 with
                                                    | (e1, uu____10731, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____10666
                                  FStar_List.unzip in
                              (match uu____10657 with
                               | (flags, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1522_10772 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1522_10772.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1522_10772.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u) in
                                   let uu____10778 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____10778))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____10788 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____10792 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____10802 = aux u3 in
            FStar_Syntax_Syntax.U_succ uu____10802
        | FStar_Syntax_Syntax.U_max us ->
            let uu____10806 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____10806
        | FStar_Syntax_Syntax.U_name x ->
            let uu____10810 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____10810
            then u2
            else
              (let uu____10815 =
                 let uu____10817 =
                   let uu____10819 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.op_Hat uu____10819 " not found" in
                 Prims.op_Hat "Universe variable " uu____10817 in
               failwith uu____10815) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____10826 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____10826 FStar_Pervasives_Native.snd
         | uu____10835 -> aux u)
and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun top ->
      fun bs ->
        fun body ->
          let fail1 msg t =
            let uu____10866 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____10866 top.FStar_Syntax_Syntax.pos in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____10955 bs2 bs_expected1 =
              match uu____10955 with
              | (env2, subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([], []) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1, imp)::bs3, (hd_expected, imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11146),
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11147)) -> true
                           | (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality)) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11162),
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11163)) -> true
                           | uu____11172 -> false in
                         let uu____11182 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11185 =
                                FStar_Syntax_Util.eq_aqual imp imp' in
                              uu____11185 <> FStar_Syntax_Util.Equal) in
                         if uu____11182
                         then
                           let uu____11187 =
                             let uu____11193 =
                               let uu____11195 =
                                 FStar_Syntax_Print.bv_to_string hd1 in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11195 in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11193) in
                           let uu____11199 =
                             FStar_Syntax_Syntax.range_of_bv hd1 in
                           FStar_Errors.raise_error uu____11187 uu____11199
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____11203 =
                           let uu____11210 =
                             let uu____11211 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____11211.FStar_Syntax_Syntax.n in
                           match uu____11210 with
                           | FStar_Syntax_Syntax.Tm_unknown ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11222 ->
                               ((let uu____11224 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____11224
                                 then
                                   let uu____11227 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11227
                                 else ());
                                (let uu____11232 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____11232 with
                                 | (t, uu____11246, g1_env) ->
                                     let g2_env =
                                       let uu____11249 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t in
                                       if uu____11249
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11254 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t in
                                          match uu____11254 with
                                          | FStar_Pervasives_Native.None ->
                                              let uu____11257 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t in
                                              let uu____11263 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_Errors.raise_error
                                                uu____11257 uu____11263
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____11265 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____11265
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env) in
                                     let uu____11267 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env in
                                     (t, uu____11267))) in
                         match uu____11203 with
                         | (t, g_env) ->
                             let hd2 =
                               let uu___1620_11293 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1620_11293.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1620_11293.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env_b = push_binding env2 b in
                             let subst2 =
                               let uu____11316 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____11316 in
                             let uu____11319 =
                               aux (env_b, subst2) bs3 bs_expected2 in
                             (match uu____11319 with
                              | (env_bs, bs4, rest, g'_env_b, subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b in
                                  let uu____11384 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env in
                                  (env_bs, (b :: bs4), rest, uu____11384,
                                    subst3))))
                   | (rest, []) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ([], rest) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1)) in
            aux (env1, []) bs1 bs_expected in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____11556 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11566 = tc_binders env1 bs in
                  match uu____11566 with
                  | (bs1, envbody, g_env, uu____11596) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____11652 =
                    let uu____11653 = FStar_Syntax_Subst.compress t2 in
                    uu____11653.FStar_Syntax_Syntax.n in
                  match uu____11652 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11686 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11706 -> failwith "Impossible");
                       (let uu____11716 = tc_binders env1 bs in
                        match uu____11716 with
                        | (bs1, envbody, g_env, uu____11758) ->
                            let uu____11759 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____11759 with
                             | (envbody1, uu____11797) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____11818;
                         FStar_Syntax_Syntax.pos = uu____11819;
                         FStar_Syntax_Syntax.vars = uu____11820;_},
                       uu____11821)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11865 -> failwith "Impossible");
                       (let uu____11875 = tc_binders env1 bs in
                        match uu____11875 with
                        | (bs1, envbody, g_env, uu____11917) ->
                            let uu____11918 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____11918 with
                             | (envbody1, uu____11956) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____11978) ->
                      let uu____11983 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____11983 with
                       | (uu____12044, bs1, bs', copt, env_body, body2,
                          g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                      let uu____12121 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____12121 with
                       | (bs_expected1, c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12266 c_expected2
                               body3 =
                               match uu____12266 with
                               | (env_bs, bs2, more, guard_env, subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None ->
                                        let uu____12380 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env_bs, bs2, guard_env, uu____12380,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12397 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12397 in
                                        let uu____12398 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env_bs, bs2, guard_env, uu____12398,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____12415 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____12415
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env_bs
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3, c_expected3) ->
                                               let uu____12481 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____12481 with
                                                | (bs_expected4, c_expected4)
                                                    ->
                                                    let uu____12508 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4 in
                                                    (match uu____12508 with
                                                     | (env_bs_bs', bs',
                                                        more1, guard'_env_bs,
                                                        subst2) ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs in
                                                         let uu____12563 =
                                                           let uu____12590 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12590,
                                                             subst2) in
                                                         handle_more
                                                           uu____12563
                                                           c_expected4 body3))
                                           | uu____12613 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None in
                                               (env_bs, bs2, guard_env, c,
                                                 body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None in
                                           (env_bs, bs2, guard_env, c, body4))) in
                             let uu____12642 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____12642 c_expected1 body2 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___1746_12707 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1746_12707.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1746_12707.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1746_12707.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1746_12707.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1746_12707.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1746_12707.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1746_12707.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1746_12707.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1746_12707.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1746_12707.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1746_12707.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1746_12707.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1746_12707.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1746_12707.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1746_12707.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1746_12707.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1746_12707.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1746_12707.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1746_12707.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1746_12707.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1746_12707.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1746_12707.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1746_12707.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1746_12707.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1746_12707.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1746_12707.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1746_12707.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1746_12707.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1746_12707.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1746_12707.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1746_12707.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1746_12707.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1746_12707.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1746_12707.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1746_12707.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1746_12707.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1746_12707.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1746_12707.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1746_12707.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1746_12707.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1746_12707.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1746_12707.FStar_TypeChecker_Env.nbe)
                               } in
                             let uu____12714 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____12780 ->
                                       fun uu____12781 ->
                                         match (uu____12780, uu____12781)
                                         with
                                         | ((env2, letrec_binders, g),
                                            (l, t3, u_names)) ->
                                             let uu____12872 =
                                               let uu____12879 =
                                                 let uu____12880 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2 in
                                                 FStar_All.pipe_right
                                                   uu____12880
                                                   FStar_Pervasives_Native.fst in
                                               tc_term uu____12879 t3 in
                                             (match uu____12872 with
                                              | (t4, uu____12904, g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4) in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____12917 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1764_12920
                                                               = x in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1764_12920.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1764_12920.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             }) in
                                                        uu____12917 ::
                                                          letrec_binders
                                                    | uu____12921 ->
                                                        letrec_binders in
                                                  let uu____12926 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g' in
                                                  (env3, lb, uu____12926)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard)) in
                             match uu____12714 with
                             | (envbody2, letrec_binders, g) ->
                                 let uu____12946 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g in
                                 (envbody2, letrec_binders, uu____12946) in
                           let uu____12949 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1 in
                           (match uu____12949 with
                            | (envbody, bs1, g_env, c, body2) ->
                                let uu____13025 = mk_letrec_env envbody bs1 c in
                                (match uu____13025 with
                                 | (envbody1, letrecs, g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     let uu____13072 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13072))))
                  | uu____13089 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13121 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____13121
                      else
                        (let uu____13125 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____13125 with
                         | (uu____13174, bs1, uu____13176, c_opt, envbody,
                            body2, g_env) ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____13208 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____13208 with
          | (env1, topt) ->
              ((let uu____13228 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____13228
                then
                  let uu____13231 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13231
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13245 = expected_function_typ1 env1 topt body in
                match uu____13245 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____13286 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____13286
                      then
                        let uu____13291 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____13294 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13291 uu____13294
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____13300 =
                        let should_check_expected_effect =
                          let uu____13313 =
                            let uu____13320 =
                              let uu____13321 =
                                FStar_Syntax_Subst.compress body1 in
                              uu____13321.FStar_Syntax_Syntax.n in
                            (c_opt, uu____13320) in
                          match uu____13313 with
                          | (FStar_Pervasives_Native.None,
                             FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13327,
                              (FStar_Util.Inr expected_c, uu____13329),
                              uu____13330)) -> false
                          | uu____13380 -> true in
                        let uu____13388 =
                          tc_term
                            (let uu___1826_13397 = envbody1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1826_13397.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1826_13397.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1826_13397.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1826_13397.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1826_13397.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1826_13397.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1826_13397.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1826_13397.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1826_13397.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1826_13397.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1826_13397.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1826_13397.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1826_13397.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1826_13397.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1826_13397.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1826_13397.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1826_13397.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1826_13397.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1826_13397.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1826_13397.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1826_13397.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1826_13397.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1826_13397.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1826_13397.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1826_13397.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1826_13397.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1826_13397.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1826_13397.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1826_13397.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1826_13397.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1826_13397.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1826_13397.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1826_13397.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1826_13397.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1826_13397.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1826_13397.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1826_13397.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1826_13397.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1826_13397.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1826_13397.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1826_13397.FStar_TypeChecker_Env.nbe)
                             }) body1 in
                        match uu____13388 with
                        | (body2, cbody, guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body in
                            if should_check_expected_effect
                            then
                              let uu____13424 =
                                let uu____13431 =
                                  let uu____13436 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody in
                                  (body2, uu____13436) in
                                check_expected_effect
                                  (let uu___1834_13439 = envbody1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___1834_13439.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___1834_13439.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___1834_13439.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___1834_13439.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___1834_13439.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___1834_13439.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___1834_13439.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___1834_13439.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___1834_13439.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___1834_13439.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___1834_13439.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___1834_13439.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___1834_13439.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___1834_13439.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___1834_13439.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___1834_13439.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___1834_13439.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___1834_13439.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___1834_13439.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___1834_13439.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___1834_13439.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___1834_13439.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___1834_13439.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___1834_13439.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___1834_13439.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___1834_13439.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___1834_13439.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___1834_13439.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___1834_13439.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___1834_13439.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___1834_13439.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___1834_13439.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___1834_13439.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___1834_13439.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___1834_13439.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___1834_13439.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___1834_13439.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___1834_13439.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___1834_13439.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___1834_13439.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___1834_13439.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___1834_13439.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____13431 in
                              (match uu____13424 with
                               | (body3, cbody1, guard) ->
                                   let uu____13453 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard in
                                   (body3, cbody1, uu____13453))
                            else
                              (let uu____13460 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody in
                               (body2, uu____13460, guard_body1)) in
                      match uu____13300 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____13485 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13488 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____13488) in
                            if uu____13485
                            then
                              let uu____13491 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____13492 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____13491
                                uu____13492
                            else
                              (let guard =
                                 let uu____13496 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13496 in
                               guard) in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              bs1 guard in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt))) in
                          let uu____13510 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13531
                                     -> (e, t1, guard1)
                                 | uu____13546 ->
                                     let uu____13547 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1 in
                                     (match uu____13547 with
                                      | (e1, guard') ->
                                          let uu____13560 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t1, uu____13560)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____13510 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____13571 =
                                 let uu____13576 =
                                   FStar_Syntax_Util.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13576 guard2 in
                               (match uu____13571 with
                                | (c1, g) -> (e1, c1, g)))))))
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
  fun env ->
    fun head1 ->
      fun chead ->
        fun ghead ->
          fun args ->
            fun expected_topt ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = chead.FStar_Syntax_Syntax.res_typ in
              (let uu____13625 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____13625
               then
                 let uu____13628 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____13630 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13628
                   uu____13630
               else ());
              (let monadic_application uu____13708 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____13708 with
                 | (head2, chead1, ghead1, cres) ->
                     let uu____13769 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     (match uu____13769 with
                      | (rt, g0) ->
                          let cres1 =
                            let uu___1894_13783 = cres in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___1894_13783.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___1894_13783.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___1894_13783.FStar_Syntax_Syntax.comp_thunk)
                            } in
                          let uu____13784 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____13800 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____13800 in
                                (cres1, g)
                            | uu____13801 ->
                                let g =
                                  let uu____13811 =
                                    let uu____13812 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____13812
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____13811 in
                                let uu____13813 =
                                  let uu____13814 =
                                    let uu____13815 =
                                      let uu____13816 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1 in
                                      FStar_Syntax_Util.arrow bs uu____13816 in
                                    FStar_Syntax_Syntax.mk_Total uu____13815 in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____13814 in
                                (uu____13813, g) in
                          (match uu____13784 with
                           | (cres2, guard1) ->
                               ((let uu____13828 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low in
                                 if uu____13828
                                 then
                                   let uu____13831 =
                                     FStar_Syntax_Print.lcomp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____13831
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____13851 ->
                                             match uu____13851 with
                                             | (uu____13861, uu____13862, lc)
                                                 ->
                                                 (let uu____13870 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc in
                                                  Prims.op_Negation
                                                    uu____13870)
                                                   ||
                                                   (FStar_TypeChecker_Util.should_not_inline_lc
                                                      lc)) arg_comps_rev) in
                                   let term =
                                     FStar_Syntax_Syntax.mk_Tm_app head2
                                       (FStar_List.rev arg_rets_rev)
                                       FStar_Pervasives_Native.None
                                       head2.FStar_Syntax_Syntax.pos in
                                   let uu____13883 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful in
                                   if uu____13883
                                   then
                                     ((let uu____13887 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____13887
                                       then
                                         let uu____13890 =
                                           FStar_Syntax_Print.term_to_string
                                             term in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____13890
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____13898 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____13898
                                       then
                                         let uu____13901 =
                                           FStar_Syntax_Print.term_to_string
                                             term in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____13901
                                       else ());
                                      cres2) in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c ->
                                        fun uu____13932 ->
                                          match uu____13932 with
                                          | ((e, q), x, c) ->
                                              ((let uu____13974 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme in
                                                if uu____13974
                                                then
                                                  let uu____13977 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                        -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1 in
                                                  let uu____13982 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e in
                                                  let uu____13984 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____13977 uu____13982
                                                    uu____13984
                                                else ());
                                               (let uu____13989 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c in
                                                if uu____13989
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
                                     arg_comps_rev in
                                 let comp1 =
                                   (let uu____14000 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme in
                                    if uu____14000
                                    then
                                      let uu____14003 =
                                        FStar_Syntax_Print.term_to_string
                                          head2 in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____14003
                                    else ());
                                   (let uu____14008 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1 in
                                    if uu____14008
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
                                        (FStar_Pervasives_Native.None, comp)) in
                                 let comp2 =
                                   FStar_TypeChecker_Util.subst_lcomp subst1
                                     comp1 in
                                 let shortcuts_evaluation_order =
                                   let uu____14020 =
                                     let uu____14021 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____14021.FStar_Syntax_Syntax.n in
                                   match uu____14020 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____14026 -> false in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1 ->
                                            fun uu____14049 ->
                                              match uu____14049 with
                                              | (arg, uu____14063,
                                                 uu____14064) -> arg :: args1)
                                         [] arg_comps_rev in
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head2
                                         args1 FStar_Pervasives_Native.None r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.res_typ in
                                     FStar_TypeChecker_Util.maybe_monadic env
                                       app1
                                       comp2.FStar_Syntax_Syntax.eff_name
                                       comp2.FStar_Syntax_Syntax.res_typ
                                   else
                                     (let uu____14075 =
                                        let map_fun uu____14141 =
                                          match uu____14141 with
                                          | ((e, q), uu____14182, c) ->
                                              ((let uu____14205 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme in
                                                if uu____14205
                                                then
                                                  let uu____14208 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e in
                                                  let uu____14210 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____14208 uu____14210
                                                else ());
                                               (let uu____14215 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c in
                                                if uu____14215
                                                then
                                                  ((let uu____14241 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14241
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
                                                       (let uu____14282 =
                                                          let uu____14284 =
                                                            let uu____14285 =
                                                              FStar_Syntax_Util.un_uinst
                                                                head2 in
                                                            uu____14285.FStar_Syntax_Syntax.n in
                                                          match uu____14284
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let uu____14290
                                                                =
                                                                FStar_Parser_Const.psconst
                                                                  "ignore" in
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv
                                                                uu____14290
                                                          | uu____14292 ->
                                                              true in
                                                        Prims.op_Negation
                                                          uu____14282) in
                                                   if warn_effectful_args
                                                   then
                                                     (let uu____14296 =
                                                        let uu____14302 =
                                                          let uu____14304 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e in
                                                          let uu____14306 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head2 in
                                                          FStar_Util.format3
                                                            "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                            uu____14304
                                                            (c.FStar_Syntax_Syntax.eff_name).FStar_Ident.str
                                                            uu____14306 in
                                                        (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                          uu____14302) in
                                                      FStar_Errors.log_issue
                                                        e.FStar_Syntax_Syntax.pos
                                                        uu____14296)
                                                   else ();
                                                   (let uu____14313 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____14313
                                                    then
                                                      FStar_Util.print_string
                                                        "... lifting!\n"
                                                    else ());
                                                   (let x =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        c.FStar_Syntax_Syntax.res_typ in
                                                    let e1 =
                                                      FStar_TypeChecker_Util.maybe_lift
                                                        env e
                                                        c.FStar_Syntax_Syntax.eff_name
                                                        comp2.FStar_Syntax_Syntax.eff_name
                                                        c.FStar_Syntax_Syntax.res_typ in
                                                    let uu____14321 =
                                                      let uu____14330 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      (uu____14330, q) in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____14321))))) in
                                        let uu____14359 =
                                          let uu____14390 =
                                            let uu____14419 =
                                              let uu____14430 =
                                                let uu____14439 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2 in
                                                (uu____14439,
                                                  FStar_Pervasives_Native.None,
                                                  chead1) in
                                              uu____14430 :: arg_comps_rev in
                                            FStar_List.map map_fun
                                              uu____14419 in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____14390 in
                                        match uu____14359 with
                                        | (lifted_args, reverse_args) ->
                                            let uu____14640 =
                                              let uu____14641 =
                                                FStar_List.hd reverse_args in
                                              FStar_Pervasives_Native.fst
                                                uu____14641 in
                                            let uu____14662 =
                                              let uu____14663 =
                                                FStar_List.tl reverse_args in
                                              FStar_List.rev uu____14663 in
                                            (lifted_args, uu____14640,
                                              uu____14662) in
                                      match uu____14075 with
                                      | (lifted_args, head3, args1) ->
                                          let app =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head3 args1
                                              FStar_Pervasives_Native.None r in
                                          let app1 =
                                            FStar_TypeChecker_Util.maybe_lift
                                              env app
                                              cres3.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ in
                                          let app2 =
                                            FStar_TypeChecker_Util.maybe_monadic
                                              env app1
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ in
                                          let bind_lifted_args e uu___6_14774
                                            =
                                            match uu___6_14774 with
                                            | FStar_Pervasives_Native.None ->
                                                e
                                            | FStar_Pervasives_Native.Some
                                                (x, m, t, e1) ->
                                                let lb =
                                                  FStar_Syntax_Util.mk_letbinding
                                                    (FStar_Util.Inl x) [] t m
                                                    e1 []
                                                    e1.FStar_Syntax_Syntax.pos in
                                                let letbinding =
                                                  let uu____14835 =
                                                    let uu____14842 =
                                                      let uu____14843 =
                                                        let uu____14857 =
                                                          let uu____14860 =
                                                            let uu____14861 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____14861] in
                                                          FStar_Syntax_Subst.close
                                                            uu____14860 e in
                                                        ((false, [lb]),
                                                          uu____14857) in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____14843 in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____14842 in
                                                  uu____14835
                                                    FStar_Pervasives_Native.None
                                                    e.FStar_Syntax_Syntax.pos in
                                                FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_meta
                                                     (letbinding,
                                                       (FStar_Syntax_Syntax.Meta_monadic
                                                          (m,
                                                            (comp2.FStar_Syntax_Syntax.res_typ)))))
                                                  FStar_Pervasives_Native.None
                                                  e.FStar_Syntax_Syntax.pos in
                                          FStar_List.fold_left
                                            bind_lifted_args app2 lifted_args) in
                                 let uu____14913 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1 in
                                 match uu____14913 with
                                 | (comp3, g) ->
                                     ((let uu____14931 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____14931
                                       then
                                         let uu____14934 =
                                           FStar_Syntax_Print.term_to_string
                                             app in
                                         let uu____14936 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3 in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____14934 uu____14936
                                       else ());
                                      (app, comp3, g)))))) in
               let rec tc_args head_info uu____15017 bs args1 =
                 match uu____15017 with
                 | (subst1, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15156))::rest,
                         (uu____15158, FStar_Pervasives_Native.None)::uu____15159)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____15220 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          (match uu____15220 with
                           | (t1, g_ex) ->
                               let uu____15233 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1 in
                               (match uu____15233 with
                                | (varg, uu____15254, implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1 in
                                    let arg =
                                      let uu____15282 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____15282) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____15291 =
                                      let uu____15326 =
                                        let uu____15337 =
                                          let uu____15346 =
                                            let uu____15347 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____15347
                                              FStar_Syntax_Util.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15346) in
                                        uu____15337 :: outargs in
                                      (subst2, uu____15326, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____15291 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,
                         (uu____15393, FStar_Pervasives_Native.None)::uu____15394)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau in
                          let uu____15456 = tc_tactic env tau1 in
                          (match uu____15456 with
                           | (tau2, uu____15470, g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____15473 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t in
                               (match uu____15473 with
                                | (t1, g_ex) ->
                                    let uu____15486 =
                                      let uu____15499 =
                                        let uu____15506 =
                                          let uu____15511 =
                                            FStar_Dyn.mkdyn env in
                                          (uu____15511, tau2) in
                                        FStar_Pervasives_Native.Some
                                          uu____15506 in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15499 in
                                    (match uu____15486 with
                                     | (varg, uu____15524, implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1 in
                                         let arg =
                                           let uu____15552 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____15552) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits in
                                         let uu____15561 =
                                           let uu____15596 =
                                             let uu____15607 =
                                               let uu____15616 =
                                                 let uu____15617 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____15617
                                                   FStar_Syntax_Util.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15616) in
                                             uu____15607 :: outargs in
                                           (subst2, uu____15596, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____15561 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____15733, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15734)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15745),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15746)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15754),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15755)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____15770 ->
                                let uu____15779 =
                                  let uu____15785 =
                                    let uu____15787 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____15789 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____15791 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____15793 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____15787 uu____15789 uu____15791
                                      uu____15793 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____15785) in
                                FStar_Errors.raise_error uu____15779
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual in
                            let x1 =
                              let uu___2104_15800 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2104_15800.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2104_15800.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____15802 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____15802
                             then
                               let uu____15805 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____15807 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____15809 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____15811 =
                                 FStar_Syntax_Print.subst_to_string subst1 in
                               let uu____15813 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____15805 uu____15807 uu____15809
                                 uu____15811 uu____15813
                             else ());
                            (let uu____15818 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             match uu____15818 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___2113_15833 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2113_15833.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2113_15833.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2113_15833.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2113_15833.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2113_15833.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2113_15833.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2113_15833.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2113_15833.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2113_15833.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2113_15833.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2113_15833.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2113_15833.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2113_15833.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2113_15833.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2113_15833.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2113_15833.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2113_15833.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2113_15833.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2113_15833.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2113_15833.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2113_15833.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2113_15833.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2113_15833.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2113_15833.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2113_15833.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2113_15833.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2113_15833.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2113_15833.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2113_15833.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2113_15833.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2113_15833.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2113_15833.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2113_15833.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2113_15833.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2113_15833.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2113_15833.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2113_15833.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2113_15833.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2113_15833.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2113_15833.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2113_15833.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2113_15833.FStar_TypeChecker_Env.nbe)
                                   } in
                                 ((let uu____15835 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____15835
                                   then
                                     let uu____15838 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____15840 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____15842 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____15838 uu____15840 uu____15842
                                   else ());
                                  (let uu____15847 = tc_term env2 e in
                                   match uu____15847 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____15864 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____15864 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____15887 =
                                           let uu____15890 =
                                             let uu____15899 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15899 in
                                           FStar_Pervasives_Native.fst
                                             uu____15890 in
                                         (uu____15887, aq) in
                                       let uu____15908 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name) in
                                       if uu____15908
                                       then
                                         let subst2 =
                                           let uu____15918 = FStar_List.hd bs in
                                           maybe_extend_subst subst1
                                             uu____15918 e1 in
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
                      | (uu____16017, []) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____16053) ->
                          let uu____16104 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____16104 with
                           | (head2, chead1, ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____16160 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____16160
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1, cres')
                                     ->
                                     let uu____16191 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____16191 with
                                      | (bs2, cres'1) ->
                                          let head_info1 =
                                            let uu____16213 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1 in
                                            (head2, chead1, ghead2,
                                              uu____16213) in
                                          ((let uu____16215 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____16215
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
                                 | uu____16262 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2 in
                                       let uu____16270 =
                                         let uu____16271 =
                                           FStar_Syntax_Subst.compress tres3 in
                                         uu____16271.FStar_Syntax_Syntax.n in
                                       match uu____16270 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____16274;
                                              FStar_Syntax_Syntax.index =
                                                uu____16275;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},
                                            uu____16277)
                                           -> norm_tres tres4
                                       | uu____16285 -> tres3 in
                                     let uu____16286 = norm_tres tres1 in
                                     aux true solve ghead2 uu____16286
                                 | uu____16288 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2 in
                                     aux norm1 true ghead3 tres1
                                 | uu____16291 ->
                                     let uu____16292 =
                                       let uu____16298 =
                                         let uu____16300 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead in
                                         let uu____16302 =
                                           FStar_Util.string_of_int n_args in
                                         let uu____16304 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1 in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____16300 uu____16302
                                           uu____16304 in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____16298) in
                                     let uu____16308 =
                                       FStar_Syntax_Syntax.argpos arg in
                                     FStar_Errors.raise_error uu____16292
                                       uu____16308 in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf guard =
                 let uu____16338 =
                   let uu____16339 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____16339.FStar_Syntax_Syntax.n in
                 match uu____16338 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16348 ->
                     let uu____16361 =
                       FStar_List.fold_right
                         (fun uu____16392 ->
                            fun uu____16393 ->
                              match uu____16393 with
                              | (bs, guard1) ->
                                  let uu____16420 =
                                    let uu____16433 =
                                      let uu____16434 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____16434
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16433 in
                                  (match uu____16420 with
                                   | (t, uu____16451, g) ->
                                       let uu____16465 =
                                         let uu____16468 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____16468 :: bs in
                                       let uu____16469 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____16465, uu____16469))) args
                         ([], guard) in
                     (match uu____16361 with
                      | (bs, guard1) ->
                          let uu____16486 =
                            let uu____16493 =
                              let uu____16506 =
                                let uu____16507 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____16507
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16506 in
                            match uu____16493 with
                            | (t, uu____16524, g) ->
                                let uu____16538 = FStar_Options.ml_ish () in
                                if uu____16538
                                then
                                  let uu____16547 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____16550 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____16547, uu____16550)
                                else
                                  (let uu____16555 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____16558 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____16555, uu____16558)) in
                          (match uu____16486 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____16577 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____16577
                                 then
                                   let uu____16581 =
                                     FStar_Syntax_Print.term_to_string head1 in
                                   let uu____16583 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____16585 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16581 uu____16583 uu____16585
                                 else ());
                                (let g =
                                   let uu____16591 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16591 in
                                 let uu____16592 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____16592))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16593;
                        FStar_Syntax_Syntax.pos = uu____16594;
                        FStar_Syntax_Syntax.vars = uu____16595;_},
                      uu____16596)
                     ->
                     let uu____16633 =
                       FStar_List.fold_right
                         (fun uu____16664 ->
                            fun uu____16665 ->
                              match uu____16665 with
                              | (bs, guard1) ->
                                  let uu____16692 =
                                    let uu____16705 =
                                      let uu____16706 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____16706
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16705 in
                                  (match uu____16692 with
                                   | (t, uu____16723, g) ->
                                       let uu____16737 =
                                         let uu____16740 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____16740 :: bs in
                                       let uu____16741 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____16737, uu____16741))) args
                         ([], guard) in
                     (match uu____16633 with
                      | (bs, guard1) ->
                          let uu____16758 =
                            let uu____16765 =
                              let uu____16778 =
                                let uu____16779 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____16779
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16778 in
                            match uu____16765 with
                            | (t, uu____16796, g) ->
                                let uu____16810 = FStar_Options.ml_ish () in
                                if uu____16810
                                then
                                  let uu____16819 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____16822 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____16819, uu____16822)
                                else
                                  (let uu____16827 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____16830 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____16827, uu____16830)) in
                          (match uu____16758 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____16849 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____16849
                                 then
                                   let uu____16853 =
                                     FStar_Syntax_Print.term_to_string head1 in
                                   let uu____16855 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____16857 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16853 uu____16855 uu____16857
                                 else ());
                                (let g =
                                   let uu____16863 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16863 in
                                 let uu____16864 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____16864))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____16887 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____16887 with
                      | (bs1, c1) ->
                          let head_info =
                            let uu____16909 =
                              FStar_Syntax_Util.lcomp_of_comp c1 in
                            (head1, chead, ghead, uu____16909) in
                          ((let uu____16911 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____16911
                            then
                              let uu____16914 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16916 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____16918 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____16921 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____16914 uu____16916 uu____16918
                                uu____16921
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____16967) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____16973, uu____16974) ->
                     check_function_app t guard
                 | uu____17015 ->
                     let uu____17016 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____17016
                       head1.FStar_Syntax_Syntax.pos in
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
  fun env ->
    fun head1 ->
      fun chead ->
        fun g_head ->
          fun args ->
            fun expected_topt ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____17099 =
                    FStar_List.fold_left2
                      (fun uu____17168 ->
                         fun uu____17169 ->
                           fun uu____17170 ->
                             match (uu____17168, uu____17169, uu____17170)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____17323 =
                                     let uu____17325 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____17325 <> FStar_Syntax_Util.Equal in
                                   if uu____17323
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17331 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____17331 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____17360 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17360 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17365 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____17365)
                                              &&
                                              (let uu____17368 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____17368)) in
                                       let uu____17370 =
                                         let uu____17381 =
                                           let uu____17392 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____17392] in
                                         FStar_List.append seen uu____17381 in
                                       let uu____17425 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____17370, uu____17425, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____17099 with
                   | (args1, guard, ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____17493 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____17493
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____17496 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____17496 with | (c2, g) -> (e, c2, g)))
              | uu____17513 ->
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
  fun env ->
    fun pat_t ->
      fun p0 ->
        let fail1 msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t in
            let uu____17604 = FStar_Syntax_Util.head_and_args t1 in
            match uu____17604 with
            | (head1, args) ->
                let uu____17647 =
                  let uu____17648 = FStar_Syntax_Subst.compress head1 in
                  uu____17648.FStar_Syntax_Syntax.n in
                (match uu____17647 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____17652;
                        FStar_Syntax_Syntax.vars = uu____17653;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____17660 ->
                     if norm1
                     then t1
                     else
                       (let uu____17664 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____17664))
          and unfold_once t f us args =
            let uu____17682 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____17682
            then t
            else
              (let uu____17687 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____17687 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____17707 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____17707 with
                    | (uu____17712, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____17719 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____17719 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____17738 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____17738
           then
             let uu____17743 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____17745 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____17743 uu____17745
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____17765 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____17767 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____17765 uu____17767 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____17771 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____17771 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____17815 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____17815 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____17816;
                    FStar_Syntax_Syntax.pos = uu____17817;
                    FStar_Syntax_Syntax.vars = uu____17818;_} ->
                    let uu____17821 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____17821 with
                     | (head_p, args_p) ->
                         let uu____17864 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____17864
                         then
                           let uu____17867 =
                             let uu____17868 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____17868.FStar_Syntax_Syntax.n in
                           (match uu____17867 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____17873 =
                                    let uu____17875 =
                                      let uu____17877 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____17877 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____17875 in
                                  if uu____17873
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____17905 =
                                    let uu____17930 =
                                      let uu____17934 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____17934 in
                                    match uu____17930 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____17983 =
                                          FStar_Util.first_N n1 args_p in
                                        (match uu____17983 with
                                         | (params_p, uu____18041) ->
                                             let uu____18082 =
                                               FStar_Util.first_N n1 args_s in
                                             (match uu____18082 with
                                              | (params_s, uu____18140) ->
                                                  (params_p, params_s))) in
                                  match uu____17905 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____18269 ->
                                             fun uu____18270 ->
                                               match (uu____18269,
                                                       uu____18270)
                                               with
                                               | ((p, uu____18304),
                                                  (s, uu____18306)) ->
                                                   let uu____18339 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____18339 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____18342 =
                                                          let uu____18344 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____18346 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18344
                                                            uu____18346 in
                                                        fail2 uu____18342
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____18351 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18355 =
                              let uu____18357 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____18359 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18357 uu____18359 in
                            fail2 uu____18355))
                | uu____18362 ->
                    let uu____18363 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____18363 with
                     | FStar_Pervasives_Native.None -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____18400 = FStar_Syntax_Util.head_and_args e in
          match uu____18400 with
          | (head1, args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18464 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18464 with
                    | (us, t_f) ->
                        let uu____18481 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____18481 with
                         | (formals, t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18610 formals1 args1 =
                                 match uu____18610 with
                                 | (subst1, args_out, bvs, guard) ->
                                     (match (formals1, args1) with
                                      | ([], []) ->
                                          let head2 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head1 us in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head2 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos in
                                          let uu____18755 =
                                            FStar_Syntax_Subst.subst subst1 t in
                                          (pat_e, uu____18755, bvs, guard)
                                      | ((f1, uu____18761)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____18819 =
                                            let uu____18840 =
                                              let uu____18841 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____18841.FStar_Syntax_Syntax.n in
                                            match uu____18840 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2413_18866 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2413_18866.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2413_18866.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  } in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1 in
                                                let subst2 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst1 in
                                                ((a1, imp_a), subst2,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____18889 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____18903 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____18903 with
                                                 | (a1, uu____18931, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst2 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst1 in
                                                     ((a1, imp_a), subst2,
                                                       bvs, g1))
                                            | uu____18955 ->
                                                fail1 "Not a simple pattern" in
                                          (match uu____18819 with
                                           | (a1, subst2, bvs1, g) ->
                                               let uu____19017 =
                                                 let uu____19040 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19040) in
                                               aux uu____19017 formals2 args2)
                                      | uu____19079 ->
                                          fail1 "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19135 -> fail1 "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____19184 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____19184
           then
             let uu____19189 = FStar_Syntax_Print.pat_to_string p in
             let uu____19191 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19189
               uu____19191
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19206 ->
               let uu____19213 =
                 let uu____19215 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19215 in
               failwith uu____19213
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2445_19230 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2445_19230.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2445_19230.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____19231 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], uu____19231,
                 (let uu___2448_19235 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2448_19235.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2452_19238 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2452_19238.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2452_19238.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____19239 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], uu____19239,
                 (let uu___2455_19243 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2455_19243.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19244 ->
               let uu____19245 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
               (match uu____19245 with
                | (uu____19267, e_c, uu____19269, uu____19270) ->
                    let uu____19275 = tc_tot_or_gtot_term env1 e_c in
                    (match uu____19275 with
                     | (e_c1, lc, g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t in
                           (let uu____19298 =
                              let uu____19300 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t in
                              Prims.op_Negation uu____19300 in
                            if uu____19298
                            then
                              let uu____19303 =
                                let uu____19305 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ in
                                let uu____19307 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19305 uu____19307 in
                              fail1 uu____19303
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19365 ->
                        match uu____19365 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19395
                                 -> (p1, b)
                             | uu____19405 ->
                                 let uu____19406 =
                                   let uu____19409 =
                                     let uu____19410 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____19410 in
                                   FStar_Syntax_Syntax.withinfo uu____19409
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____19406, b))) sub_pats in
                 let uu___2483_19414 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2483_19414.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19459 ->
                         match uu____19459 with
                         | (x, uu____19469) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19477
                                  -> false
                              | uu____19485 -> true))) in
               let uu____19487 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____19487 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19524 =
                          let uu____19526 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____19528 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____19530 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____19537 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19526 uu____19528 uu____19530 uu____19537 in
                        failwith uu____19524)
                     else ();
                     (let uu____19542 =
                        let uu____19551 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____19551 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard)
                            ->
                            let g' =
                              let uu____19579 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____19579 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____19582 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____19582
                              then
                                let uu____19587 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____19589 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____19591 =
                                  let uu____19593 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____19601 =
                                           let uu____19603 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____19605 =
                                             let uu____19607 =
                                               let uu____19609 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.op_Hat uu____19609 ")" in
                                             Prims.op_Hat " : " uu____19607 in
                                           Prims.op_Hat uu____19603
                                             uu____19605 in
                                         Prims.op_Hat "(" uu____19601)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____19593
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19587 uu____19589 uu____19591
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1)) in
                      match uu____19542 with
                      | (simple_pat_e1, simple_bvs1, g1) ->
                          let uu____19641 =
                            let uu____19663 =
                              let uu____19685 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], uu____19685) in
                            FStar_List.fold_left2
                              (fun uu____19746 ->
                                 fun uu____19747 ->
                                   fun x ->
                                     match (uu____19746, uu____19747) with
                                     | ((env2, bvs, pats, subst1, g),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____19880 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____19880 with
                                          | (bvs_p, e_p, p2, g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let uu____19921 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____19921))) uu____19663
                              sub_pats1 simple_bvs1 in
                          (match uu____19641 with
                           | (_env, bvs, checked_sub_pats, subst1, g) ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst1
                                   simple_pat_e1 in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd1, b)::simple_pats1 ->
                                       (match hd1.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x, e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst1
                                                e in
                                            let hd2 =
                                              let uu___2555_20133 = hd1 in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2555_20133.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____20138 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd2, b) :: uu____20138
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd2, uu____20182)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20219 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd2, b) :: uu____20219
                                             | uu____20239 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20265 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___2576_20308 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2576_20308.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20320 -> failwith "Impossible" in
                               let uu____20324 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, pat_e, uu____20324, g)))))) in
        (let uu____20328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____20328
         then
           let uu____20333 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20333
         else ());
        (let uu____20338 =
           let uu____20349 =
             let uu___2581_20350 =
               let uu____20351 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____20351 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2581_20350.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2581_20350.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2581_20350.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2581_20350.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2581_20350.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2581_20350.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2581_20350.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2581_20350.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2581_20350.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2581_20350.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2581_20350.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2581_20350.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2581_20350.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2581_20350.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2581_20350.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2581_20350.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2581_20350.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2581_20350.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2581_20350.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2581_20350.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2581_20350.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2581_20350.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2581_20350.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2581_20350.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2581_20350.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2581_20350.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2581_20350.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2581_20350.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2581_20350.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2581_20350.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2581_20350.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2581_20350.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2581_20350.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2581_20350.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2581_20350.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2581_20350.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2581_20350.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2581_20350.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2581_20350.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2581_20350.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2581_20350.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2581_20350.FStar_TypeChecker_Env.nbe)
             } in
           let uu____20367 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____20349 uu____20367 pat_t in
         match uu____20338 with
         | (bvs, pat_e, pat, g) ->
             ((let uu____20391 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____20391
               then
                 let uu____20396 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____20398 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20396
                   uu____20398
               else ());
              (let uu____20403 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____20404 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, uu____20403, pat_e, uu____20404, g))))
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
  fun scrutinee ->
    fun env ->
      fun branch1 ->
        let uu____20450 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____20450 with
        | (pattern, when_clause, branch_exp) ->
            let uu____20496 = branch1 in
            (match uu____20496 with
             | (cpat, uu____20538, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____20560 =
                   let uu____20567 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____20567
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____20560 with
                  | (scrutinee_env, uu____20601) ->
                      let uu____20606 = tc_pat env pat_t pattern in
                      (match uu____20606 with
                       | (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp,
                          guard_pat) ->
                           let uu____20657 =
                             match when_clause with
                             | FStar_Pervasives_Native.None ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____20687 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____20687
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____20710 =
                                      let uu____20717 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____20717 e in
                                    match uu____20710 with
                                    | (e1, c, g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____20657 with
                            | (when_clause1, g_when) ->
                                let uu____20771 = tc_term pat_env branch_exp in
                                (match uu____20771 with
                                 | (branch_exp1, c, g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____20827 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool in
                                             FStar_All.pipe_left
                                               (fun _20838 ->
                                                  FStar_Pervasives_Native.Some
                                                    _20838) uu____20827 in
                                       let uu____20839 =
                                         let eqs =
                                           let uu____20861 =
                                             let uu____20863 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env in
                                             Prims.op_Negation uu____20863 in
                                           if uu____20861
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____20879 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____20894 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____20897 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____20900 ->
                                                  let uu____20901 =
                                                    let uu____20904 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____20904 pat_t
                                                      scrutinee_tm e in
                                                  FStar_Pervasives_Native.Some
                                                    uu____20901) in
                                         let uu____20907 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch in
                                         match uu____20907 with
                                         | (c1, g_branch1) ->
                                             let uu____20934 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____20951 when
                                                   let uu____20964 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____20964
                                                   -> (c1, g_when)
                                               | (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None)
                                                   -> (c1, g_when)
                                               | (FStar_Pervasives_Native.Some
                                                  f,
                                                  FStar_Pervasives_Native.None)
                                                   ->
                                                   let gf =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       gf in
                                                   let uu____20995 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf in
                                                   let uu____20996 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when in
                                                   (uu____20995, uu____20996)
                                               | (FStar_Pervasives_Native.Some
                                                  f,
                                                  FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f in
                                                   let g_fw =
                                                     let uu____21017 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21017 in
                                                   let uu____21018 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw in
                                                   let uu____21019 =
                                                     let uu____21020 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21020 g_when in
                                                   (uu____21018, uu____21019)
                                               | (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_w =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       w in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       g_w in
                                                   let uu____21038 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w in
                                                   (uu____21038, g_when) in
                                             (match uu____20934 with
                                              | (c_weak, g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1 in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21081 =
                                                        should_return1 &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak) in
                                                      if uu____21081
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1 in
                                                  let uu____21086 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak in
                                                  let uu____21087 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1 in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21086, uu____21087)) in
                                       match uu____20839 with
                                       | (effect_label, cflags,
                                          maybe_return_c, g_when1, g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21138 =
                                               let uu____21140 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env in
                                               Prims.op_Negation uu____21140 in
                                             if uu____21138
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21194 =
                                                      let uu____21202 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21202 in
                                                    match uu____21194 with
                                                    | (is_induc, datacons) ->
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
                                                              f.FStar_Syntax_Syntax.v in
                                                          let uu____21218 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator in
                                                          (match uu____21218
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                               -> []
                                                           | uu____21239 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                   FStar_Pervasives_Native.None in
                                                               let disc1 =
                                                                 let uu____21255
                                                                   =
                                                                   let uu____21260
                                                                    =
                                                                    let uu____21261
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                    [uu____21261] in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21260 in
                                                                 uu____21255
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                               let uu____21286
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool in
                                                               [uu____21286])
                                                        else [] in
                                                  let fail1 uu____21294 =
                                                    let uu____21295 =
                                                      let uu____21297 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos in
                                                      let uu____21299 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1 in
                                                      let uu____21301 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1 in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21297
                                                        uu____21299
                                                        uu____21301 in
                                                    failwith uu____21295 in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1, uu____21316) ->
                                                        head_constructor t1
                                                    | uu____21321 -> fail1 () in
                                                  let force_scrutinee
                                                    uu____21327 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____21328 =
                                                          let uu____21330 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p in
                                                          let uu____21332 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2 in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21330
                                                            uu____21332 in
                                                        failwith uu____21328
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t in
                                                  let pat_exp2 =
                                                    let uu____21339 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1 in
                                                    FStar_All.pipe_right
                                                      uu____21339
                                                      FStar_Syntax_Util.unmeta in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21344,
                                                     FStar_Syntax_Syntax.Tm_name
                                                     uu____21345) -> []
                                                  | (uu____21346,
                                                     FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit))
                                                      -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,
                                                     FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21349 =
                                                        let uu____21350 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1 in
                                                        let uu____21351 =
                                                          force_scrutinee () in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21350
                                                          uu____21351
                                                          pat_exp2 in
                                                      [uu____21349]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21352,
                                                      FStar_Pervasives_Native.Some
                                                      uu____21353)),
                                                     uu____21354) ->
                                                      let uu____21371 =
                                                        let uu____21378 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env in
                                                        match uu____21378
                                                        with
                                                        | (env1, uu____21392)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2 in
                                                      (match uu____21371 with
                                                       | (uu____21399, t,
                                                          uu____21401) ->
                                                           let uu____21402 =
                                                             let uu____21403
                                                               =
                                                               force_scrutinee
                                                                 () in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21403
                                                               pat_exp2 in
                                                           [uu____21402])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21404, []),
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21405) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2 in
                                                      let uu____21429 =
                                                        let uu____21431 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v in
                                                        Prims.op_Negation
                                                          uu____21431 in
                                                      if uu____21429
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21441 =
                                                           force_scrutinee () in
                                                         let uu____21444 =
                                                           head_constructor
                                                             pat_exp2 in
                                                         discriminate
                                                           uu____21441
                                                           uu____21444)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21447, []),
                                                     FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21448) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2 in
                                                      let uu____21466 =
                                                        let uu____21468 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v in
                                                        Prims.op_Negation
                                                          uu____21468 in
                                                      if uu____21466
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21478 =
                                                           force_scrutinee () in
                                                         let uu____21481 =
                                                           head_constructor
                                                             pat_exp2 in
                                                         discriminate
                                                           uu____21478
                                                           uu____21481)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21484, pat_args),
                                                     FStar_Syntax_Syntax.Tm_app
                                                     (head1, args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1 in
                                                      let uu____21531 =
                                                        (let uu____21535 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v in
                                                         Prims.op_Negation
                                                           uu____21535)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args)) in
                                                      if uu____21531
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21563 =
                                                             let uu____21568
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args in
                                                             FStar_All.pipe_right
                                                               uu____21568
                                                               (FStar_List.mapi
                                                                  (fun i ->
                                                                    fun
                                                                    uu____21654
                                                                    ->
                                                                    match uu____21654
                                                                    with
                                                                    | 
                                                                    ((pi,
                                                                    uu____21676),
                                                                    (ei,
                                                                    uu____21678))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____21706
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    match uu____21706
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____21727
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____21739
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____21739
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____21741
                                                                    =
                                                                    let uu____21742
                                                                    =
                                                                    let uu____21747
                                                                    =
                                                                    let uu____21748
                                                                    =
                                                                    let uu____21757
                                                                    =
                                                                    force_scrutinee
                                                                    () in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____21757 in
                                                                    [uu____21748] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____21747 in
                                                                    uu____21742
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____21741 in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei)) in
                                                           FStar_All.pipe_right
                                                             uu____21563
                                                             FStar_List.flatten in
                                                         let uu____21780 =
                                                           let uu____21783 =
                                                             force_scrutinee
                                                               () in
                                                           discriminate
                                                             uu____21783 f in
                                                         FStar_List.append
                                                           uu____21780
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____21786,
                                                     uu____21787) -> []
                                                  | uu____21794 ->
                                                      let uu____21799 =
                                                        let uu____21801 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2 in
                                                        let uu____21803 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2 in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____21801
                                                          uu____21803 in
                                                      failwith uu____21799 in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____21832 =
                                                    let uu____21834 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env in
                                                    Prims.op_Negation
                                                      uu____21834 in
                                                  if uu____21832
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____21840 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____21840 in
                                                     let uu____21849 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     match uu____21849 with
                                                     | (k, uu____21855) ->
                                                         let uu____21856 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k in
                                                         (match uu____21856
                                                          with
                                                          | (t1, uu____21864,
                                                             uu____21865) ->
                                                              t1)) in
                                                let branch_guard =
                                                  build_and_check_branch_guard
                                                    (FStar_Pervasives_Native.Some
                                                       scrutinee_tm) pattern1
                                                    norm_pat_exp in
                                                let branch_guard1 =
                                                  match when_condition with
                                                  | FStar_Pervasives_Native.None
                                                      -> branch_guard
                                                  | FStar_Pervasives_Native.Some
                                                      w ->
                                                      FStar_Syntax_Util.mk_conj
                                                        branch_guard w in
                                                branch_guard1) in
                                           let guard =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_when1 g_branch1 in
                                           ((let uu____21877 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High in
                                             if uu____21877
                                             then
                                               let uu____21880 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____21880
                                             else ());
                                            (let uu____21886 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1) in
                                             let uu____21903 =
                                               let uu____21904 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1 in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____21904 guard in
                                             (uu____21886, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____21903))))))))))
and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let uu____21951 = check_let_bound_def true env1 lb in
          (match uu____21951 with
           | (e1, univ_vars1, c1, g1, annotated) ->
               let uu____21977 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____21999 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____21999, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22005 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____22005
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____22006 =
                      let uu____22019 =
                        let uu____22034 =
                          let uu____22043 =
                            let uu____22050 =
                              FStar_Syntax_Syntax.lcomp_comp c1 in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____22050) in
                          [uu____22043] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____22034 in
                      FStar_List.hd uu____22019 in
                    match uu____22006 with
                    | (uu____22086, univs1, e11, c11, gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta;
                               FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                               FStar_TypeChecker_Env.CompressUvars;
                               FStar_TypeChecker_Env.NoFullNorm;
                               FStar_TypeChecker_Env.Exclude
                                 FStar_TypeChecker_Env.Zeta] env1) in
                        let g13 =
                          FStar_TypeChecker_Env.abstract_guard_n gvs g12 in
                        let uu____22100 = FStar_Syntax_Util.lcomp_of_comp c11 in
                        (g13, e11, univs1, uu____22100)) in
               (match uu____21977 with
                | (g11, e11, univ_vars2, c11) ->
                    let uu____22117 =
                      let uu____22126 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____22126
                      then
                        let uu____22137 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____22137 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22171 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____22171
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22172 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____22172, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____22187 =
                              FStar_Syntax_Syntax.lcomp_comp c11 in
                            FStar_All.pipe_right uu____22187
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1) in
                          let e21 =
                            let uu____22193 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____22193
                            then e2
                            else
                              ((let uu____22201 =
                                  FStar_TypeChecker_Env.get_range env1 in
                                FStar_Errors.log_issue uu____22201
                                  FStar_TypeChecker_Err.top_level_effect);
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect)))
                                 FStar_Pervasives_Native.None
                                 e2.FStar_Syntax_Syntax.pos) in
                          (e21, c))) in
                    (match uu____22117 with
                     | (e21, c12) ->
                         ((let uu____22225 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____22225
                           then
                             let uu____22228 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22228
                           else ());
                          (let e12 =
                             let uu____22234 = FStar_Options.tcnorm () in
                             if uu____22234
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
                             else e11 in
                           (let uu____22240 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____22240
                            then
                              let uu____22243 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22243
                            else ());
                           (let cres =
                              FStar_TypeChecker_Env.null_wp_for_eff env1
                                (FStar_Syntax_Util.comp_effect_name c12)
                                FStar_Syntax_Syntax.U_zero
                                FStar_Syntax_Syntax.t_unit in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars2
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos in
                            let uu____22252 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos in
                            let uu____22266 =
                              FStar_Syntax_Util.lcomp_of_comp cres in
                            (uu____22252, uu____22266,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22267 -> failwith "Impossible"
and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env ->
    fun lem_typ ->
      fun c2 ->
        let uu____22278 = FStar_Syntax_Util.is_smt_lemma lem_typ in
        if uu____22278
        then
          let universe_of_binders bs =
            let uu____22305 =
              FStar_List.fold_left
                (fun uu____22330 ->
                   fun b ->
                     match uu____22330 with
                     | (env1, us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         (env2, (u :: us))) (env, []) bs in
            match uu____22305 with | (uu____22378, us) -> FStar_List.rev us in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2
and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let env2 =
            let uu___2893_22414 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2893_22414.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2893_22414.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2893_22414.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2893_22414.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2893_22414.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2893_22414.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2893_22414.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2893_22414.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2893_22414.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2893_22414.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2893_22414.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2893_22414.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2893_22414.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2893_22414.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2893_22414.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2893_22414.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2893_22414.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2893_22414.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2893_22414.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2893_22414.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2893_22414.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2893_22414.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2893_22414.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2893_22414.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2893_22414.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2893_22414.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2893_22414.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2893_22414.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2893_22414.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2893_22414.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2893_22414.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2893_22414.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2893_22414.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2893_22414.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2893_22414.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2893_22414.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2893_22414.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2893_22414.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2893_22414.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2893_22414.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2893_22414.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2893_22414.FStar_TypeChecker_Env.nbe)
            } in
          let uu____22416 =
            let uu____22428 =
              let uu____22429 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____22429 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____22428 lb in
          (match uu____22416 with
           | (e1, uu____22452, c1, g1, annotated) ->
               let pure_or_ghost =
                 FStar_Syntax_Util.is_pure_or_ghost_lcomp c1 in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____22466 =
                     let uu____22472 =
                       let uu____22474 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____22476 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____22474 uu____22476 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____22472) in
                   FStar_Errors.raise_error uu____22466
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____22487 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_Syntax_Syntax.res_typ) in
                   if uu____22487
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs in
                 let x =
                   let uu___2908_22499 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2908_22499.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2908_22499.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   } in
                 let uu____22500 =
                   let uu____22505 =
                     let uu____22506 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____22506] in
                   FStar_Syntax_Subst.open_term uu____22505 e2 in
                 match uu____22500 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____22550 = tc_term env_x e21 in
                     (match uu____22550 with
                      | (e22, c2, g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_Syntax_Syntax.res_typ c2 in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21) in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c21.FStar_Syntax_Syntax.res_typ in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_Syntax_Syntax.res_typ
                              cres.FStar_Syntax_Syntax.eff_name e11 attrs
                              lb.FStar_Syntax_Syntax.lbpos in
                          let e3 =
                            let uu____22576 =
                              let uu____22583 =
                                let uu____22584 =
                                  let uu____22598 =
                                    FStar_Syntax_Subst.close xb e23 in
                                  ((false, [lb1]), uu____22598) in
                                FStar_Syntax_Syntax.Tm_let uu____22584 in
                              FStar_Syntax_Syntax.mk uu____22583 in
                            uu____22576 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ in
                          let x_eq_e1 =
                            let uu____22616 =
                              let uu____22617 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ in
                              let uu____22618 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              FStar_Syntax_Util.mk_eq2 uu____22617
                                c1.FStar_Syntax_Syntax.res_typ uu____22618
                                e11 in
                            FStar_All.pipe_left
                              (fun _22619 ->
                                 FStar_TypeChecker_Common.NonTrivial _22619)
                              uu____22616 in
                          let g21 =
                            let uu____22621 =
                              let uu____22622 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1 in
                              FStar_TypeChecker_Env.imp_guard uu____22622 g2 in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____22621 in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22 in
                          let uu____22625 =
                            let uu____22627 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____22627 in
                          if uu____22625
                          then
                            let tt =
                              let uu____22638 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____22638
                                FStar_Option.get in
                            ((let uu____22644 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____22644
                              then
                                let uu____22649 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____22651 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____22649 uu____22651
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____22658 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                             match uu____22658 with
                             | (t, g_ex) ->
                                 ((let uu____22672 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____22672
                                   then
                                     let uu____22677 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ in
                                     let uu____22679 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____22677 uu____22679
                                   else ());
                                  (let uu____22684 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___2941_22686 = cres in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___2941_22686.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___2941_22686.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___2941_22686.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____22684))))))))
      | uu____22687 ->
          failwith "Impossible (inner let with more than one lb)"
and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____22723 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____22723 with
           | (lbs1, e21) ->
               let uu____22742 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____22742 with
                | (env0, topt) ->
                    let uu____22761 = build_let_rec_env true env0 lbs1 in
                    (match uu____22761 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____22784 = check_let_recs rec_env lbs2 in
                         (match uu____22784 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____22804 =
                                  let uu____22805 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____22805
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____22804
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____22811 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____22811
                                  (fun _22828 ->
                                     FStar_Pervasives_Native.Some _22828) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef in
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
                                     let uu____22865 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____22899 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____22899))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____22865 in
                                   FStar_List.map2
                                     (fun uu____22934 ->
                                        fun lb ->
                                          match uu____22934 with
                                          | (x, uvs, e, c, gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3) in
                              let cres =
                                let uu____22982 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____22982 in
                              let uu____22983 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____22983 with
                               | (lbs5, e22) ->
                                   ((let uu____23003 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____23003
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23004 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____23004, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23018 -> failwith "Impossible"
and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____23054 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____23054 with
           | (lbs1, e21) ->
               let uu____23073 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____23073 with
                | (env0, topt) ->
                    let uu____23092 = build_let_rec_env false env0 lbs1 in
                    (match uu____23092 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____23115 =
                           let uu____23122 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____23122
                             (fun uu____23145 ->
                                match uu____23145 with
                                | (lbs3, g) ->
                                    let uu____23164 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____23164)) in
                         (match uu____23115 with
                          | (lbs3, g_lbs) ->
                              let uu____23179 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___3016_23202 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3016_23202.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3016_23202.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___3019_23204 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3019_23204.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____23179 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____23231 = tc_term env2 e21 in
                                   (match uu____23231 with
                                    | (e22, cres, g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb ->
                                               fun cres1 ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1 in
                                        let cres3 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____23255 =
                                            let uu____23256 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23256 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23255 in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres3 in
                                        let tres =
                                          norm env2
                                            cres4.FStar_Syntax_Syntax.res_typ in
                                        let cres5 =
                                          let uu___3040_23266 = cres4 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___3040_23266.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___3040_23266.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___3040_23266.FStar_Syntax_Syntax.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____23274 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____23274)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard in
                                        let uu____23275 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____23275 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____23316 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____23317 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____23317 with
                                                   | (tres1, g_ex) ->
                                                       let cres6 =
                                                         let uu___3056_23331
                                                           = cres5 in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___3056_23331.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___3056_23331.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___3056_23331.FStar_Syntax_Syntax.comp_thunk)
                                                         } in
                                                       let uu____23332 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres6,
                                                         uu____23332))))))))))
      | uu____23333 -> failwith "Impossible"
and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t))
  =
  fun top_level ->
    fun env ->
      fun lbs ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____23381 = FStar_Options.ml_ish () in
          if uu____23381
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____23389 = FStar_Syntax_Util.arrow_formals_comp t in
             match uu____23389 with
             | (formals, c) ->
                 let uu____23421 = FStar_Syntax_Util.abs_formals lbdef in
                 (match uu____23421 with
                  | (actuals, uu____23432, uu____23433) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____23454 =
                          let uu____23460 =
                            let uu____23462 =
                              FStar_Syntax_Print.term_to_string lbdef in
                            let uu____23464 =
                              FStar_Syntax_Print.term_to_string lbtyp in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____23462 uu____23464 in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____23460) in
                        FStar_Errors.raise_error uu____23454
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____23472 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____23472 actuals in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1 in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____23503 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____23503) in
                            let formals_msg =
                              let n1 = FStar_List.length formals in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____23522 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments"
                                   uu____23522) in
                            let msg =
                              let uu____23527 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              let uu____23529 =
                                FStar_Syntax_Print.lbname_to_string lbname in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____23527 uu____23529 formals_msg
                                actuals_msg in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c) in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect))))) in
        let uu____23541 =
          FStar_List.fold_left
            (fun uu____23574 ->
               fun lb ->
                 match uu____23574 with
                 | (lbs1, env1, g_acc) ->
                     let uu____23599 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____23599 with
                      | (univ_vars1, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1 in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____23622 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1 in
                               let uu____23641 =
                                 let uu____23648 =
                                   let uu____23649 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____23649 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3102_23660 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3102_23660.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3102_23660.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3102_23660.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3102_23660.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3102_23660.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3102_23660.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3102_23660.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3102_23660.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3102_23660.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3102_23660.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3102_23660.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3102_23660.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3102_23660.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3102_23660.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3102_23660.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3102_23660.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3102_23660.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3102_23660.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3102_23660.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3102_23660.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3102_23660.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3102_23660.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3102_23660.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3102_23660.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3102_23660.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3102_23660.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3102_23660.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3102_23660.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3102_23660.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3102_23660.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3102_23660.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3102_23660.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3102_23660.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3102_23660.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3102_23660.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3102_23660.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3102_23660.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3102_23660.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3102_23660.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3102_23660.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3102_23660.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3102_23660.FStar_TypeChecker_Env.nbe)
                                    }) t uu____23648 in
                               match uu____23641 with
                               | (t1, uu____23669, g) ->
                                   let uu____23671 =
                                     let uu____23672 =
                                       let uu____23673 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____23673
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____23672 in
                                   let uu____23674 = norm env01 t1 in
                                   (uu____23671, uu____23674)) in
                          (match uu____23622 with
                           | (g, t1) ->
                               let env3 =
                                 let uu____23694 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 if uu____23694
                                 then
                                   let uu___3112_23697 = env2 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3112_23697.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3112_23697.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3112_23697.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3112_23697.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3112_23697.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3112_23697.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3112_23697.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3112_23697.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3112_23697.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3112_23697.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3112_23697.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3112_23697.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3112_23697.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3112_23697.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3112_23697.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3112_23697.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3112_23697.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3112_23697.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3112_23697.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3112_23697.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3112_23697.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3112_23697.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3112_23697.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3112_23697.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3112_23697.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3112_23697.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3112_23697.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3112_23697.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3112_23697.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3112_23697.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3112_23697.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3112_23697.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3112_23697.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3112_23697.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3112_23697.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3112_23697.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3112_23697.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3112_23697.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3112_23697.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3112_23697.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3112_23697.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3112_23697.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1) in
                               let lb1 =
                                 let uu___3115_23711 = lb in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3115_23711.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3115_23711.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3115_23711.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3115_23711.FStar_Syntax_Syntax.lbpos)
                                 } in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____23541 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun lbs ->
      let uu____23737 =
        let uu____23746 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____23772 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____23772 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____23802 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____23802
                       | uu____23809 ->
                           let lb1 =
                             let uu___3132_23812 = lb in
                             let uu____23813 =
                               FStar_Syntax_Util.abs bs t lcomp in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____23813;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3132_23812.FStar_Syntax_Syntax.lbpos)
                             } in
                           let uu____23816 =
                             let uu____23823 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp in
                             tc_tot_or_gtot_term uu____23823
                               lb1.FStar_Syntax_Syntax.lbdef in
                           (match uu____23816 with
                            | (e, c, g) ->
                                ((let uu____23832 =
                                    let uu____23834 =
                                      FStar_Syntax_Util.is_total_lcomp c in
                                    Prims.op_Negation uu____23834 in
                                  if uu____23832
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
                                      lb1.FStar_Syntax_Syntax.lbpos in
                                  (lb2, g))))))) in
        FStar_All.pipe_right uu____23746 FStar_List.unzip in
      match uu____23737 with
      | (lbs1, gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard in
          (lbs1, g_lbs)
and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t *
          Prims.bool))
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let uu____23890 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____23890 with
        | (env1, uu____23909) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____23917 = check_lbtyp top_level env lb in
            (match uu____23917 with
             | (topt, wf_annot, univ_vars1, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____23966 =
                     tc_maybe_toplevel_term
                       (let uu___3163_23975 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3163_23975.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3163_23975.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3163_23975.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3163_23975.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3163_23975.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3163_23975.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3163_23975.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3163_23975.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3163_23975.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3163_23975.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3163_23975.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3163_23975.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3163_23975.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3163_23975.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3163_23975.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3163_23975.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3163_23975.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3163_23975.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3163_23975.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3163_23975.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3163_23975.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3163_23975.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3163_23975.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3163_23975.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3163_23975.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3163_23975.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3163_23975.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3163_23975.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3163_23975.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3163_23975.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3163_23975.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3163_23975.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3163_23975.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3163_23975.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3163_23975.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3163_23975.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3163_23975.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3163_23975.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3163_23975.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3163_23975.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3163_23975.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3163_23975.FStar_TypeChecker_Env.nbe)
                        }) e11 in
                   match uu____23966 with
                   | (e12, c1, g1) ->
                       let uu____23990 =
                         let uu____23995 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24001 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____23995 e12 c1 wf_annot in
                       (match uu____23990 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____24018 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____24018
                              then
                                let uu____24021 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____24023 =
                                  FStar_Syntax_Print.lcomp_to_string c11 in
                                let uu____24025 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24021 uu____24023 uu____24025
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
  fun top_level ->
    fun env ->
      fun lb ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____24064 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____24064 with
             | (univ_opening, univ_vars1) ->
                 let uu____24097 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24097))
        | uu____24102 ->
            let uu____24103 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____24103 with
             | (univ_opening, univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24153 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24153)
                 else
                   (let uu____24160 = FStar_Syntax_Util.type_u () in
                    match uu____24160 with
                    | (k, uu____24180) ->
                        let uu____24181 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____24181 with
                         | (t2, uu____24203, g) ->
                             ((let uu____24206 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____24206
                               then
                                 let uu____24209 =
                                   let uu____24211 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____24211 in
                                 let uu____24212 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24209 uu____24212
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____24218 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24218))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env ->
    fun uu____24224 ->
      match uu____24224 with
      | (x, imp) ->
          let uu____24251 = FStar_Syntax_Util.type_u () in
          (match uu____24251 with
           | (tu, u) ->
               ((let uu____24273 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____24273
                 then
                   let uu____24276 = FStar_Syntax_Print.bv_to_string x in
                   let uu____24278 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____24280 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____24276 uu____24278 uu____24280
                 else ());
                (let uu____24285 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____24285 with
                 | (t, uu____24307, g) ->
                     let uu____24309 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____24325 = tc_tactic env tau in
                           (match uu____24325 with
                            | (tau1, uu____24339, g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____24343 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____24309 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___3225_24378 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3225_24378.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3225_24378.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____24380 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____24380
                            then
                              let uu____24383 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____24387 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____24383
                                uu____24387
                            else ());
                           (let uu____24392 = push_binding env x1 in
                            (x1, uu____24392, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun bs ->
      (let uu____24404 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____24404
       then
         let uu____24407 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____24407
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____24520 = tc_binder env1 b in
             (match uu____24520 with
              | (b1, env', g, u) ->
                  let uu____24569 = aux env' bs2 in
                  (match uu____24569 with
                   | (bs3, env'1, g', us) ->
                       let uu____24630 =
                         let uu____24631 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____24631 in
                       ((b1 :: bs3), env'1, uu____24630, (u :: us)))) in
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
  fun en ->
    fun pats ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____24739 ->
             fun uu____24740 ->
               match (uu____24739, uu____24740) with
               | ((t, imp), (args1, g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____24832 = tc_term en1 t in
                     match uu____24832 with
                     | (t1, uu____24852, g') ->
                         let uu____24854 =
                           FStar_TypeChecker_Env.conj_guard g g' in
                         (((t1, imp) :: args1), uu____24854)))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____24908 ->
             match uu____24908 with
             | (pats1, g) ->
                 let uu____24935 = tc_args en p in
                 (match uu____24935 with
                  | (args, g') ->
                      let uu____24948 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____24948))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)
and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      let uu____24961 = tc_maybe_toplevel_term env e in
      match uu____24961 with
      | (e1, c, g) ->
          let uu____24977 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____24977
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c in
             let c2 = norm_c env c1 in
             let uu____24991 =
               let uu____24997 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____24997
               then
                 let uu____25005 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____25005, false)
               else
                 (let uu____25010 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____25010, true)) in
             match uu____24991 with
             | (target_comp, allow_ghost) ->
                 let uu____25023 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____25023 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____25033 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp in
                      let uu____25034 =
                        FStar_TypeChecker_Env.conj_guard g1 g' in
                      (e1, uu____25033, uu____25034)
                  | uu____25035 ->
                      if allow_ghost
                      then
                        let uu____25045 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2 in
                        FStar_Errors.raise_error uu____25045
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____25059 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2 in
                         FStar_Errors.raise_error uu____25059
                           e1.FStar_Syntax_Syntax.pos)))
and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      fun t ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env ->
    fun t ->
      let uu____25083 = tc_tot_or_gtot_term env t in
      match uu____25083 with
      | (t1, c, g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun e ->
      (let uu____25116 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____25116
       then
         let uu____25121 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____25121
       else ());
      (let env1 =
         let uu___3307_25127 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3307_25127.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3307_25127.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3307_25127.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3307_25127.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3307_25127.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3307_25127.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3307_25127.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3307_25127.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3307_25127.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3307_25127.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3307_25127.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3307_25127.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3307_25127.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3307_25127.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3307_25127.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3307_25127.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3307_25127.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3307_25127.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3307_25127.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3307_25127.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3307_25127.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3307_25127.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3307_25127.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3307_25127.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3307_25127.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3307_25127.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3307_25127.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3307_25127.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3307_25127.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3307_25127.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3307_25127.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3307_25127.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3307_25127.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3307_25127.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3307_25127.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3307_25127.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3307_25127.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3307_25127.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3307_25127.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3307_25127.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3307_25127.FStar_TypeChecker_Env.nbe)
         } in
       let uu____25135 =
         try
           (fun uu___3311_25149 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____25170) ->
             let uu____25173 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____25173 in
       match uu____25135 with
       | (t, c, g) ->
           let uu____25190 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____25190
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____25201 =
                let uu____25207 =
                  let uu____25209 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25209 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25207) in
              let uu____25213 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____25201 uu____25213))
let level_of_type_fail :
  'Auu____25229 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25229
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____25247 =
          let uu____25253 =
            let uu____25255 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____25255 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25253) in
        let uu____25259 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____25247 uu____25259
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____25293 =
            let uu____25294 = FStar_Syntax_Util.unrefine t1 in
            uu____25294.FStar_Syntax_Syntax.n in
          match uu____25293 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____25298 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____25304 = FStar_Syntax_Util.type_u () in
                 match uu____25304 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___3342_25312 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3342_25312.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3342_25312.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3342_25312.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3342_25312.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3342_25312.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3342_25312.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3342_25312.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3342_25312.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3342_25312.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3342_25312.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3342_25312.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3342_25312.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3342_25312.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3342_25312.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3342_25312.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3342_25312.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3342_25312.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3342_25312.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3342_25312.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3342_25312.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3342_25312.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3342_25312.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3342_25312.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3342_25312.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3342_25312.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3342_25312.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3342_25312.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3342_25312.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3342_25312.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3342_25312.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3342_25312.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3342_25312.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3342_25312.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3342_25312.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3342_25312.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3342_25312.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3342_25312.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3342_25312.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3342_25312.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3342_25312.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3342_25312.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3342_25312.FStar_TypeChecker_Env.nbe)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25317 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____25317
                       | uu____25319 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun e ->
      let uu____25336 =
        let uu____25337 = FStar_Syntax_Subst.compress e in
        uu____25337.FStar_Syntax_Syntax.n in
      match uu____25336 with
      | FStar_Syntax_Syntax.Tm_bvar uu____25340 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____25343 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____25367 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____25384) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____25429) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____25436 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____25436 with | ((uu____25445, t), uu____25447) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____25453 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____25453
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25456, (FStar_Util.Inl t, uu____25458), uu____25459) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25506, (FStar_Util.Inr c, uu____25508), uu____25509) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____25557 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____25566;
             FStar_Syntax_Syntax.vars = uu____25567;_},
           us)
          ->
          let uu____25573 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____25573 with
           | ((us', t), uu____25584) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____25591 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____25591)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____25610 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____25612 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____25621) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____25648 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____25648 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____25668 ->
                      match uu____25668 with
                      | (b, uu____25676) ->
                          let uu____25681 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____25681) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____25686 = universe_of_aux env res in
                 level_of_type env res uu____25686 in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res) in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____25797 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____25813 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____25851 ->
                let uu____25852 = universe_of_aux env hd3 in
                (uu____25852, args1)
            | FStar_Syntax_Syntax.Tm_name uu____25863 ->
                let uu____25864 = universe_of_aux env hd3 in
                (uu____25864, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____25875 ->
                let uu____25888 = universe_of_aux env hd3 in
                (uu____25888, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____25899 ->
                let uu____25906 = universe_of_aux env hd3 in
                (uu____25906, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____25917 ->
                let uu____25944 = universe_of_aux env hd3 in
                (uu____25944, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____25955 ->
                let uu____25962 = universe_of_aux env hd3 in
                (uu____25962, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____25973 ->
                let uu____25974 = universe_of_aux env hd3 in
                (uu____25974, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____25985 ->
                let uu____26000 = universe_of_aux env hd3 in
                (uu____26000, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26011 ->
                let uu____26018 = universe_of_aux env hd3 in
                (uu____26018, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26029 ->
                let uu____26030 = universe_of_aux env hd3 in
                (uu____26030, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26041, hd4::uu____26043) ->
                let uu____26108 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____26108 with
                 | (uu____26123, uu____26124, hd5) ->
                     let uu____26142 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____26142 with
                      | (hd6, args2) -> type_of_head retry hd6 args2))
            | uu____26199 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____26201 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____26201 with
                 | (hd4, args2) -> type_of_head false hd4 args2)
            | uu____26259 ->
                let uu____26260 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____26260 with
                 | (env1, uu____26282) ->
                     let env2 =
                       let uu___3503_26288 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3503_26288.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3503_26288.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3503_26288.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3503_26288.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3503_26288.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3503_26288.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3503_26288.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3503_26288.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3503_26288.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3503_26288.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3503_26288.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3503_26288.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3503_26288.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3503_26288.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3503_26288.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3503_26288.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3503_26288.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3503_26288.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3503_26288.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3503_26288.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3503_26288.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3503_26288.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3503_26288.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3503_26288.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3503_26288.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3503_26288.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3503_26288.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3503_26288.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3503_26288.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3503_26288.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3503_26288.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3503_26288.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3503_26288.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3503_26288.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3503_26288.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3503_26288.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3503_26288.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3503_26288.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3503_26288.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3503_26288.FStar_TypeChecker_Env.nbe)
                       } in
                     ((let uu____26293 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____26293
                       then
                         let uu____26298 =
                           let uu____26300 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____26300 in
                         let uu____26301 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____26298 uu____26301
                       else ());
                      (let uu____26306 = tc_term env2 hd3 in
                       match uu____26306 with
                       | (uu____26327,
                          { FStar_Syntax_Syntax.eff_name = uu____26328;
                            FStar_Syntax_Syntax.res_typ = t;
                            FStar_Syntax_Syntax.cflags = uu____26330;
                            FStar_Syntax_Syntax.comp_thunk = uu____26331;_},
                          g) ->
                           ((let uu____26345 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____26345 (fun a1 -> ()));
                            (t, args1))))) in
          let uu____26356 = type_of_head true hd1 args in
          (match uu____26356 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____26395 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____26395 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____26447 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____26447)))
      | FStar_Syntax_Syntax.Tm_match (uu____26449, hd1::uu____26451) ->
          let uu____26516 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____26516 with
           | (uu____26517, uu____26518, hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____26536, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      let uu____26583 = universe_of_aux env e in
      level_of_type env e uu____26583
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env ->
    fun tps ->
      let uu____26607 = tc_binders env tps in
      match uu____26607 with
      | (tps1, env1, g, us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____26665 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____26691 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26697 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____26697
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26699 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____26699
            (fun uu____26713 ->
               match uu____26713 with
               | (t2, uu____26721) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26723;
             FStar_Syntax_Syntax.vars = uu____26724;_},
           us)
          ->
          let uu____26730 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____26730
            (fun uu____26744 ->
               match uu____26744 with
               | (t2, uu____26752) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____26753) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____26755 = tc_constant env t1.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____26755
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____26757 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____26757
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____26762;_})
          ->
          let mk_comp =
            let uu____26806 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____26806
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____26837 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____26837
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____26907 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____26907
                 (fun u ->
                    let uu____26915 =
                      let uu____26918 =
                        let uu____26925 =
                          let uu____26926 =
                            let uu____26941 =
                              f tbody (FStar_Pervasives_Native.Some u) in
                            (bs, uu____26941) in
                          FStar_Syntax_Syntax.Tm_arrow uu____26926 in
                        FStar_Syntax_Syntax.mk uu____26925 in
                      uu____26918 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____26915))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____26978 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____26978 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27037 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____27037
                       (fun uc ->
                          let uu____27045 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____27045)
                 | (x, imp)::bs3 ->
                     let uu____27071 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____27071
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27080 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____27100) ->
          let uu____27105 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____27105
            (fun u_x ->
               let uu____27113 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____27113)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____27118;
             FStar_Syntax_Syntax.vars = uu____27119;_},
           a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____27198 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____27198 with
           | (unary_op1, uu____27218) ->
               let head1 =
                 let uu____27246 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27246 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____27294;
             FStar_Syntax_Syntax.vars = uu____27295;_},
           a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____27391 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____27391 with
           | (unary_op1, uu____27411) ->
               let head1 =
                 let uu____27439 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____27439 in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____27495;
             FStar_Syntax_Syntax.vars = uu____27496;_},
           uu____27497::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____27536;
             FStar_Syntax_Syntax.vars = uu____27537;_},
           (t2, uu____27539)::uu____27540::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
          let t_hd = type_of_well_typed_term env hd1 in
          let rec aux t_hd1 =
            let uu____27636 =
              let uu____27637 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____27637.FStar_Syntax_Syntax.n in
            match uu____27636 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____27710 = FStar_Util.first_N n_args bs in
                    match uu____27710 with
                    | (bs1, rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____27798 =
                          let uu____27803 = FStar_Syntax_Syntax.mk_Total t2 in
                          FStar_Syntax_Subst.open_comp bs1 uu____27803 in
                        (match uu____27798 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____27857 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____27857 with
                       | (bs1, c1) ->
                           let uu____27878 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____27878
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____27960 ->
                     match uu____27960 with
                     | (bs1, t2) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____28036 = FStar_Syntax_Subst.subst subst1 t2 in
                         FStar_Pervasives_Native.Some uu____28036)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____28038) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____28044, uu____28045)
                -> aux t2
            | uu____28086 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28087, (FStar_Util.Inl t2, uu____28089), uu____28090) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28137, (FStar_Util.Inr c, uu____28139), uu____28140) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____28205 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____28205
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____28213) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28218 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28241 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____28255 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____28266 = type_of_well_typed_term env t in
      match uu____28266 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____28272;
            FStar_Syntax_Syntax.vars = uu____28273;_}
          -> FStar_Pervasives_Native.Some u
      | uu____28276 -> FStar_Pervasives_Native.None
let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___3782_28304 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3782_28304.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3782_28304.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3782_28304.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3782_28304.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3782_28304.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3782_28304.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3782_28304.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3782_28304.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3782_28304.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3782_28304.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3782_28304.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3782_28304.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3782_28304.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3782_28304.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3782_28304.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3782_28304.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3782_28304.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3782_28304.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3782_28304.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3782_28304.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3782_28304.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3782_28304.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3782_28304.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3782_28304.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3782_28304.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3782_28304.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3782_28304.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3782_28304.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3782_28304.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3782_28304.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3782_28304.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3782_28304.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3782_28304.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3782_28304.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3782_28304.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3782_28304.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3782_28304.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3782_28304.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3782_28304.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3782_28304.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3782_28304.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3782_28304.FStar_TypeChecker_Env.nbe)
            } in
          let slow_check uu____28311 =
            if must_total
            then
              let uu____28313 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____28313 with | (uu____28320, uu____28321, g) -> g
            else
              (let uu____28325 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____28325 with | (uu____28332, uu____28333, g) -> g) in
          let uu____28335 = type_of_well_typed_term env2 t in
          match uu____28335 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____28340 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____28340
                then
                  let uu____28345 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____28347 = FStar_Syntax_Print.term_to_string t in
                  let uu____28349 = FStar_Syntax_Print.term_to_string k' in
                  let uu____28351 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____28345 uu____28347 uu____28349 uu____28351
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____28360 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____28360
                 then
                   let uu____28365 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____28367 = FStar_Syntax_Print.term_to_string t in
                   let uu____28369 = FStar_Syntax_Print.term_to_string k' in
                   let uu____28371 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____28365
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____28367 uu____28369 uu____28371
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total ->
    fun env ->
      fun t ->
        fun k ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___3813_28408 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3813_28408.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3813_28408.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3813_28408.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3813_28408.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3813_28408.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3813_28408.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3813_28408.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3813_28408.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3813_28408.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3813_28408.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3813_28408.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3813_28408.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3813_28408.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3813_28408.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3813_28408.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3813_28408.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3813_28408.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3813_28408.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3813_28408.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3813_28408.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3813_28408.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3813_28408.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3813_28408.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3813_28408.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3813_28408.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3813_28408.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3813_28408.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3813_28408.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3813_28408.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3813_28408.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3813_28408.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3813_28408.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3813_28408.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3813_28408.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3813_28408.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3813_28408.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3813_28408.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3813_28408.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3813_28408.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3813_28408.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3813_28408.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3813_28408.FStar_TypeChecker_Env.nbe)
            } in
          let slow_check uu____28415 =
            if must_total
            then
              let uu____28417 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____28417 with | (uu____28424, uu____28425, g) -> g
            else
              (let uu____28429 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____28429 with | (uu____28436, uu____28437, g) -> g) in
          let uu____28439 =
            let uu____28441 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____28441 in
          if uu____28439
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k