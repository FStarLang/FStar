open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___345_6 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___345_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___345_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___345_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___345_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___345_6.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___345_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___345_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___345_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___345_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___345_6.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___345_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___345_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___345_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___345_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___345_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___345_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___345_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___345_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___345_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___345_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___345_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___345_6.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___345_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___345_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___345_6.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___345_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___345_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___345_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___345_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___345_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___345_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___345_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___345_6.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___345_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___345_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___345_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___345_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___345_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___345_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___345_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___345_6.FStar_TypeChecker_Env.nbe)
    }
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env ->
    let uu___346_12 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___346_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___346_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___346_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___346_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___346_12.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___346_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___346_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___346_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___346_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___346_12.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___346_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___346_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___346_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___346_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___346_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___346_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___346_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___346_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___346_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___346_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___346_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___346_12.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___346_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___346_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___346_12.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___346_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___346_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___346_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___346_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___346_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___346_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___346_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___346_12.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___346_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___346_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___346_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___346_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___346_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___346_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___346_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___346_12.FStar_TypeChecker_Env.nbe)
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
           let uu____46 =
             let uu____51 =
               let uu____52 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____61 =
                 let uu____72 = FStar_Syntax_Syntax.as_arg tl1 in [uu____72] in
               uu____52 :: uu____61 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____51 in
           uu____46 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___338_113 ->
    match uu___338_113 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> true
    | uu____116 -> false
let steps :
  'Auu____123 . 'Auu____123 -> FStar_TypeChecker_Env.step Prims.list =
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
          (FStar_Syntax_Syntax.term, FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun head_opt ->
    fun env ->
      fun fvs ->
        fun kt ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____206 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____218 =
                  FStar_List.tryFind (fun x -> FStar_Util.set_mem x fvs') fvs in
                (match uu____218 with
                 | FStar_Pervasives_Native.None ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____242 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None ->
                                let uu____244 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____244
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____246 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____247 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____246 uu____247 in
                          let uu____248 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____248 in
                        let uu____253 =
                          let uu____266 = FStar_TypeChecker_Env.get_range env in
                          let uu____267 =
                            let uu____268 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____268 in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____266 env uu____267 in
                        match uu____253 with
                        | (s, uu____282, g0) ->
                            let uu____296 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s in
                            (match uu____296 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____305 =
                                     FStar_TypeChecker_Env.conj_guard g g0 in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____305 in
                                 (s, g1)
                             | uu____306 -> fail1 ()))) in
          aux false kt
let push_binding :
  'Auu____315 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____315) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env ->
    fun b ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv,
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s ->
    fun b ->
      fun v1 ->
        let uu____369 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____369
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
        (fun uu____391 ->
           let uu____392 = FStar_Syntax_Syntax.lcomp_comp lc in
           FStar_Syntax_Util.set_result_typ uu____392 t)
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
          (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
            FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
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
                 let uu____448 = FStar_Syntax_Syntax.mk_Total t in
                 FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                   uu____448
             | FStar_Util.Inr lc -> lc in
           let t = lc.FStar_Syntax_Syntax.res_typ in
           let uu____451 =
             let uu____458 = FStar_TypeChecker_Env.expected_typ env in
             match uu____458 with
             | FStar_Pervasives_Native.None -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____468 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t' in
                 (match uu____468 with
                  | (e1, lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____482 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____482 with
                       | (e2, g) ->
                           ((let uu____496 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____496
                             then
                               let uu____497 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____498 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____499 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____500 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____497 uu____498 uu____499 uu____500
                             else ());
                            (let msg =
                               let uu____508 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g in
                               if uu____508
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_16 ->
                                      FStar_Pervasives_Native.Some _0_16)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard in
                             let uu____530 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____530 with
                             | (lc2, g2) ->
                                 let uu____543 = set_lcomp_result lc2 t' in
                                 ((memo_tk e2 t'), uu____543, g2))))) in
           match uu____451 with | (e1, lc1, g) -> (e1, lc1, g))
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      fun lc ->
        let uu____580 = FStar_TypeChecker_Env.expected_typ env in
        match uu____580 with
        | FStar_Pervasives_Native.None ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____590 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____590 with
             | (e1, lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun copt ->
      fun ec ->
        let uu____642 = ec in
        match uu____642 with
        | (e, c) ->
            let tot_or_gtot c1 =
              let uu____665 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____665
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____667 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____667
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____669 =
              match copt with
              | FStar_Pervasives_Native.Some uu____682 -> (copt, c)
              | FStar_Pervasives_Native.None ->
                  let uu____685 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____687 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____687)) in
                  if uu____685
                  then
                    let uu____694 =
                      let uu____697 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____697 in
                    (uu____694, c)
                  else
                    (let uu____701 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____701
                     then
                       let uu____708 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____708)
                     else
                       (let uu____712 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____712
                        then
                          let uu____719 =
                            let uu____722 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____722 in
                          (uu____719, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____669 with
             | (expected_c_opt, c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____749 = FStar_Syntax_Util.lcomp_of_comp c2 in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____749 in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3 in
                      ((let uu____752 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low in
                        if uu____752
                        then
                          let uu____753 = FStar_Syntax_Print.term_to_string e in
                          let uu____754 =
                            FStar_Syntax_Print.comp_to_string c4 in
                          let uu____755 =
                            FStar_Syntax_Print.comp_to_string expected_c in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____753 uu____754 uu____755
                        else ());
                       (let uu____757 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c in
                        match uu____757 with
                        | (e1, uu____771, g) ->
                            let g1 =
                              let uu____774 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_TypeChecker_Util.label_guard uu____774
                                "could not prove post-condition" g in
                            ((let uu____776 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low in
                              if uu____776
                              then
                                let uu____777 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos in
                                let uu____778 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1 in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____777 uu____778
                              else ());
                             (let e2 =
                                FStar_TypeChecker_Util.maybe_lift env e1
                                  (FStar_Syntax_Util.comp_effect_name c4)
                                  (FStar_Syntax_Util.comp_effect_name
                                     expected_c)
                                  (FStar_Syntax_Util.comp_result c4) in
                              (e2, expected_c, g1)))))))
let no_logical_guard :
  'Auu____789 'Auu____790 .
    FStar_TypeChecker_Env.env ->
      ('Auu____789, 'Auu____790, FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____789, 'Auu____790, FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env ->
    fun uu____812 ->
      match uu____812 with
      | (te, kt, f) ->
          let uu____822 = FStar_TypeChecker_Env.guard_form f in
          (match uu____822 with
           | FStar_TypeChecker_Common.Trivial -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____830 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____835 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____830 uu____835)
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____847 = FStar_TypeChecker_Env.expected_typ env in
    match uu____847 with
    | FStar_Pervasives_Native.None ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____851 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____851
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all ->
    fun andlist ->
      fun pats ->
        let pats1 = FStar_Syntax_Util.unmeta pats in
        let uu____888 = FStar_Syntax_Util.head_and_args pats1 in
        match uu____888 with
        | (head1, args) ->
            let uu____933 =
              let uu____948 =
                let uu____949 = FStar_Syntax_Util.un_uinst head1 in
                uu____949.FStar_Syntax_Syntax.n in
              (uu____948, args) in
            (match uu____933 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____965) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____990, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____991))::(hd1,
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
                (uu____1064, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____1065))::(pat,
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
             | uu____1147 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all -> fun pats -> get_pat_vars' all false pats
let check_pat_fvs :
  'Auu____1176 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv, 'Auu____1176)
            FStar_Pervasives_Native.tuple2 Prims.list -> unit
  =
  fun rng ->
    fun env ->
      fun pats ->
        fun bs ->
          let pat_vars =
            let uu____1212 = FStar_List.map FStar_Pervasives_Native.fst bs in
            let uu____1219 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats in
            get_pat_vars uu____1212 uu____1219 in
          let uu____1220 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1247 ->
                    match uu____1247 with
                    | (b, uu____1253) ->
                        let uu____1254 = FStar_Util.set_mem b pat_vars in
                        Prims.op_Negation uu____1254)) in
          match uu____1220 with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (x, uu____1260) ->
              let uu____1265 =
                let uu____1270 =
                  let uu____1271 = FStar_Syntax_Print.bv_to_string x in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1271 in
                (FStar_Errors.Warning_PatternMissingBoundVar, uu____1270) in
              FStar_Errors.log_issue rng uu____1265
let check_smt_pat :
  'Auu____1282 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv, 'Auu____1282) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env ->
    fun t ->
      fun bs ->
        fun c ->
          let uu____1323 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____1323
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____1324;
                  FStar_Syntax_Syntax.effect_name = uu____1325;
                  FStar_Syntax_Syntax.result_typ = uu____1326;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats, uu____1330)::[];
                  FStar_Syntax_Syntax.flags = uu____1331;_}
                -> check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs
            | uu____1392 -> failwith "Impossible"
          else ()
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname, FStar_Syntax_Syntax.typ,
          FStar_Syntax_Syntax.univ_names) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun env ->
    fun actuals ->
      fun expected_c ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___347_1452 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___347_1452.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___347_1452.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___347_1452.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___347_1452.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___347_1452.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___347_1452.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___347_1452.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___347_1452.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___347_1452.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___347_1452.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___347_1452.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___347_1452.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___347_1452.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___347_1452.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___347_1452.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___347_1452.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___347_1452.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___347_1452.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___347_1452.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___347_1452.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___347_1452.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___347_1452.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___347_1452.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___347_1452.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___347_1452.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___347_1452.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___347_1452.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___347_1452.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___347_1452.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___347_1452.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___347_1452.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___347_1452.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___347_1452.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___347_1452.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___347_1452.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___347_1452.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___347_1452.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___347_1452.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___347_1452.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___347_1452.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___347_1452.FStar_TypeChecker_Env.nbe)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____1478 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____1478
               then
                 let uu____1479 =
                   FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____1480 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____1479 uu____1480
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____1511 ->
                         match uu____1511 with
                         | (b, uu____1521) ->
                             let t =
                               let uu____1527 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____1527 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____1530 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____1531 -> []
                              | uu____1546 ->
                                  let uu____1547 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____1547]))) in
               let as_lex_list dec =
                 let uu____1560 = FStar_Syntax_Util.head_and_args dec in
                 match uu____1560 with
                 | (head1, uu____1580) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1608 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____1616 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___339_1625 ->
                         match uu___339_1625 with
                         | FStar_Syntax_Syntax.DECREASES uu____1626 -> true
                         | uu____1629 -> false)) in
               match uu____1616 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1635 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   (match xs with | x::[] -> x | uu____1656 -> mk_lex_list xs)) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____1685 =
              match uu____1685 with
              | (l, t, u_names) ->
                  let uu____1709 =
                    let uu____1710 = FStar_Syntax_Subst.compress t in
                    uu____1710.FStar_Syntax_Syntax.n in
                  (match uu____1709 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1769 ->
                                 match uu____1769 with
                                 | (x, imp) ->
                                     let uu____1788 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____1788
                                     then
                                       let uu____1795 =
                                         let uu____1796 =
                                           let uu____1799 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____1799 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1796
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____1795, imp)
                                     else (x, imp))) in
                       let uu____1805 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____1805 with
                        | (formals2, c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____1826 =
                                let uu____1831 =
                                  let uu____1832 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____1841 =
                                    let uu____1852 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____1852] in
                                  uu____1832 :: uu____1841 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1831 in
                              uu____1826 FStar_Pervasives_Native.None r in
                            let uu____1887 = FStar_Util.prefix formals2 in
                            (match uu____1887 with
                             | (bs, (last1, imp)) ->
                                 let last2 =
                                   let uu___348_1950 = last1 in
                                   let uu____1951 =
                                     FStar_Syntax_Util.refine last1 precedes1 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___348_1950.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___348_1950.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1951
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____1987 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____1987
                                   then
                                     let uu____1988 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____1989 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____1990 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1988 uu____1989 uu____1990
                                   else ());
                                  (l, t', u_names))))
                   | uu____1994 ->
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
               let uu____2055 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1 in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2055)
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      (let uu____2650 = FStar_TypeChecker_Env.debug env FStar_Options.Medium in
       if uu____2650
       then
         let uu____2651 =
           let uu____2652 = FStar_TypeChecker_Env.get_range env in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2652 in
         let uu____2653 = FStar_Syntax_Print.term_to_string e in
         let uu____2654 =
           let uu____2655 = FStar_Syntax_Subst.compress e in
           FStar_Syntax_Print.tag_of_term uu____2655 in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____2651
           uu____2653 uu____2654
       else ());
      (let uu____2657 =
         FStar_Util.record_time
           (fun uu____2675 ->
              tc_maybe_toplevel_term
                (let uu___349_2678 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___349_2678.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___349_2678.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___349_2678.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___349_2678.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___349_2678.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___349_2678.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___349_2678.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___349_2678.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___349_2678.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___349_2678.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___349_2678.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___349_2678.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___349_2678.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___349_2678.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___349_2678.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___349_2678.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___349_2678.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___349_2678.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___349_2678.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___349_2678.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___349_2678.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___349_2678.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___349_2678.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___349_2678.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___349_2678.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___349_2678.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___349_2678.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___349_2678.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___349_2678.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___349_2678.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___349_2678.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___349_2678.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___349_2678.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___349_2678.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___349_2678.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___349_2678.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___349_2678.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___349_2678.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___349_2678.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___349_2678.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___349_2678.FStar_TypeChecker_Env.nbe)
                 }) e) in
       match uu____2657 with
       | (r, ms) ->
           ((let uu____2700 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____2700
             then
               ((let uu____2702 =
                   let uu____2703 = FStar_TypeChecker_Env.get_range env in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2703 in
                 let uu____2704 = FStar_Syntax_Print.term_to_string e in
                 let uu____2705 =
                   let uu____2706 = FStar_Syntax_Subst.compress e in
                   FStar_Syntax_Print.tag_of_term uu____2706 in
                 let uu____2707 = FStar_Util.string_of_int ms in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____2702 uu____2704 uu____2705 uu____2707);
                (let uu____2708 = r in
                 match uu____2708 with
                 | (e1, uu____2716, uu____2717) ->
                     let uu____2718 =
                       let uu____2719 = FStar_TypeChecker_Env.get_range env in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____2719 in
                     let uu____2720 = FStar_Syntax_Print.term_to_string e1 in
                     let uu____2721 =
                       let uu____2722 = FStar_Syntax_Subst.compress e1 in
                       FStar_Syntax_Print.tag_of_term uu____2722 in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____2718
                       uu____2720 uu____2721))
             else ());
            r))
and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      (let uu____2736 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____2736
       then
         let uu____2737 =
           let uu____2738 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2738 in
         let uu____2739 = FStar_Syntax_Print.tag_of_term top in
         let uu____2740 = FStar_Syntax_Print.term_to_string top in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2737 uu____2739
           uu____2740
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2748 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2777 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2784 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2797 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2798 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2799 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2800 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2801 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2820 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2835 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2842 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
           let projl uu___340_2858 =
             match uu___340_2858 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____2864 -> failwith "projl fail" in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____2877 =
                 let uu____2878 = FStar_Syntax_Subst.compress t in
                 uu____2878.FStar_Syntax_Syntax.n in
               match uu____2877 with
               | FStar_Syntax_Syntax.Tm_name uu____2881 -> true
               | uu____2882 -> false in
             FStar_Util.for_some
               (fun uu____2891 ->
                  match uu____2891 with
                  | (uu____2896, t) ->
                      let uu____2898 = is_name1 t in
                      Prims.op_Negation uu____2898)
               qi1.FStar_Syntax_Syntax.antiquotes in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static when non_trivial_antiquotes qi
                ->
                let e0 = e in
                let newbvs =
                  FStar_List.map
                    (fun uu____2916 ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs in
                let lbs =
                  FStar_List.map
                    (fun uu____2959 ->
                       match uu____2959 with
                       | ((bv, t), bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z in
                let qi1 =
                  let uu___350_2988 = qi in
                  let uu____2989 =
                    FStar_List.map
                      (fun uu____3017 ->
                         match uu____3017 with
                         | ((bv, uu____3033), bv') ->
                             let uu____3045 =
                               FStar_Syntax_Syntax.bv_to_name bv' in
                             (bv, uu____3045)) z in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___350_2988.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____2989
                  } in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                let e1 =
                  FStar_List.fold_left
                    (fun t ->
                       fun lb ->
                         let uu____3060 =
                           let uu____3067 =
                             let uu____3068 =
                               let uu____3081 =
                                 let uu____3084 =
                                   let uu____3085 =
                                     let uu____3092 =
                                       projl lb.FStar_Syntax_Syntax.lbname in
                                     FStar_Syntax_Syntax.mk_binder uu____3092 in
                                   [uu____3085] in
                                 FStar_Syntax_Subst.close uu____3084 t in
                               ((false, [lb]), uu____3081) in
                             FStar_Syntax_Syntax.Tm_let uu____3068 in
                           FStar_Syntax_Syntax.mk uu____3067 in
                         uu____3060 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term in
                let uu____3128 =
                  FStar_List.fold_right
                    (fun uu____3164 ->
                       fun uu____3165 ->
                         match (uu____3164, uu____3165) with
                         | ((bv, tm), (aqs_rev, guard)) ->
                             let uu____3234 = tc_term env_tm tm in
                             (match uu____3234 with
                              | (tm1, uu____3252, g) ->
                                  let uu____3254 =
                                    FStar_TypeChecker_Env.conj_guard g guard in
                                  (((bv, tm1) :: aqs_rev), uu____3254))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard) in
                (match uu____3128 with
                 | (aqs_rev, guard) ->
                     let qi1 =
                       let uu___351_3296 = qi in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___351_3296.FStar_Syntax_Syntax.qkind);
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
                let uu____3315 =
                  FStar_TypeChecker_Env.clear_expected_typ env1 in
                (match uu____3315 with
                 | (env', uu____3329) ->
                     let uu____3334 =
                       tc_term
                         (let uu___352_3343 = env' in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___352_3343.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___352_3343.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___352_3343.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___352_3343.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___352_3343.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___352_3343.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___352_3343.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___352_3343.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___352_3343.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___352_3343.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___352_3343.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___352_3343.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___352_3343.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___352_3343.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___352_3343.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___352_3343.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___352_3343.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___352_3343.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___352_3343.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___352_3343.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___352_3343.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___352_3343.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___352_3343.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___352_3343.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___352_3343.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___352_3343.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___352_3343.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___352_3343.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___352_3343.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___352_3343.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___352_3343.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___352_3343.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___352_3343.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___352_3343.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___352_3343.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___352_3343.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___352_3343.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___352_3343.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___352_3343.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___352_3343.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___352_3343.FStar_TypeChecker_Env.nbe)
                          }) qt in
                     (match uu____3334 with
                      | (qt1, uu____3351, uu____3352) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____3358 =
                            let uu____3365 =
                              let uu____3370 =
                                FStar_Syntax_Util.lcomp_of_comp c in
                              FStar_Util.Inr uu____3370 in
                            value_check_expected_typ env1 top uu____3365
                              FStar_TypeChecker_Env.trivial_guard in
                          (match uu____3358 with
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
           { FStar_Syntax_Syntax.blob = uu____3387;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____3388;
             FStar_Syntax_Syntax.ltyp = uu____3389;
             FStar_Syntax_Syntax.rng = uu____3390;_}
           ->
           let uu____3401 = FStar_Syntax_Util.unlazy top in
           tc_term env1 uu____3401
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat))
           ->
           let uu____3408 = tc_tot_or_gtot_term env1 e1 in
           (match uu____3408 with
            | (e2, c, g) ->
                let g1 =
                  let uu___353_3425 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___353_3425.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___353_3425.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___353_3425.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____3426 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____3426, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____3447 = FStar_Syntax_Util.type_u () in
           (match uu____3447 with
            | (t, u) ->
                let uu____3460 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____3460 with
                 | (e2, c, g) ->
                     let uu____3476 =
                       let uu____3493 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____3493 with
                       | (env2, uu____3517) -> tc_smt_pats env2 pats in
                     (match uu____3476 with
                      | (pats1, g') ->
                          let g'1 =
                            let uu___354_3555 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___354_3555.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___354_3555.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___354_3555.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____3556 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____3559 =
                            FStar_TypeChecker_Env.conj_guard g g'1 in
                          (uu____3556, c, uu____3559))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence))
           ->
           let uu____3565 =
             let uu____3566 = FStar_Syntax_Subst.compress e1 in
             uu____3566.FStar_Syntax_Syntax.n in
           (match uu____3565 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____3575,
                  { FStar_Syntax_Syntax.lbname = x;
                    FStar_Syntax_Syntax.lbunivs = uu____3577;
                    FStar_Syntax_Syntax.lbtyp = uu____3578;
                    FStar_Syntax_Syntax.lbeff = uu____3579;
                    FStar_Syntax_Syntax.lbdef = e11;
                    FStar_Syntax_Syntax.lbattrs = uu____3581;
                    FStar_Syntax_Syntax.lbpos = uu____3582;_}::[]),
                 e2)
                ->
                let uu____3610 =
                  let uu____3617 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____3617 e11 in
                (match uu____3610 with
                 | (e12, c1, g1) ->
                     let uu____3627 = tc_term env1 e2 in
                     (match uu____3627 with
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
                          let e3 =
                            let uu____3651 =
                              let uu____3658 =
                                let uu____3659 =
                                  let uu____3672 =
                                    let uu____3679 =
                                      let uu____3682 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos)) in
                                      [uu____3682] in
                                    (false, uu____3679) in
                                  (uu____3672, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____3659 in
                              FStar_Syntax_Syntax.mk uu____3658 in
                            uu____3651 FStar_Pervasives_Native.None
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
                          let uu____3704 =
                            FStar_TypeChecker_Env.conj_guard g1 g2 in
                          (e5, c, uu____3704)))
            | uu____3705 ->
                let uu____3706 = tc_term env1 e1 in
                (match uu____3706 with
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
           (e1, FStar_Syntax_Syntax.Meta_monadic uu____3728) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1, FStar_Syntax_Syntax.Meta_monadic_lift uu____3740) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
           let uu____3759 = tc_term env1 e1 in
           (match uu____3759 with
            | (e2, c, g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inr expected_c, topt), uu____3783) ->
           let uu____3830 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____3830 with
            | (env0, uu____3844) ->
                let uu____3849 = tc_comp env0 expected_c in
                (match uu____3849 with
                 | (expected_c1, uu____3863, g) ->
                     let uu____3865 =
                       let uu____3872 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0) in
                       tc_term uu____3872 e1 in
                     (match uu____3865 with
                      | (e2, c', g') ->
                          let uu____3882 =
                            let uu____3889 =
                              let uu____3894 =
                                FStar_Syntax_Syntax.lcomp_comp c' in
                              (e2, uu____3894) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____3889 in
                          (match uu____3882 with
                           | (e3, expected_c2, g'') ->
                               let uu____3904 = tc_tactic_opt env0 topt in
                               (match uu____3904 with
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
                                      let uu____3964 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g'' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____3964 in
                                    let uu____3965 =
                                      comp_check_expected_typ env1 e4 lc in
                                    (match uu____3965 with
                                     | (e5, c, f2) ->
                                         let final_guard =
                                           let uu____3982 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2 in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____3982 in
                                         let uu____3983 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac in
                                         (e5, c, uu____3983)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1, (FStar_Util.Inl t, topt), uu____3987) ->
           let uu____4034 = FStar_Syntax_Util.type_u () in
           (match uu____4034 with
            | (k, u) ->
                let uu____4047 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____4047 with
                 | (t1, uu____4061, f) ->
                     let uu____4063 = tc_tactic_opt env1 topt in
                     (match uu____4063 with
                      | (topt1, gtac) ->
                          let uu____4082 =
                            let uu____4089 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                            tc_term uu____4089 e1 in
                          (match uu____4082 with
                           | (e2, c, g) ->
                               let uu____4099 =
                                 let uu____4104 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____4109 ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____4104 e2 c f in
                               (match uu____4099 with
                                | (c1, f1) ->
                                    let uu____4118 =
                                      let uu____4125 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos in
                                      comp_check_expected_typ env1 uu____4125
                                        c1 in
                                    (match uu____4118 with
                                     | (e3, c2, f2) ->
                                         let final_guard =
                                           let uu____4172 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2 in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____4172 in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard in
                                         let uu____4174 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac in
                                         (e3, c2, uu____4174)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____4175;
              FStar_Syntax_Syntax.vars = uu____4176;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____4255 = FStar_Syntax_Util.head_and_args top in
           (match uu____4255 with
            | (unary_op1, uu____4279) ->
                let head1 =
                  let uu____4307 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4307 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____4355;
              FStar_Syntax_Syntax.vars = uu____4356;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____4435 = FStar_Syntax_Util.head_and_args top in
           (match uu____4435 with
            | (unary_op1, uu____4459) ->
                let head1 =
                  let uu____4487 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4487 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____4535);
              FStar_Syntax_Syntax.pos = uu____4536;
              FStar_Syntax_Syntax.vars = uu____4537;_},
            a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____4616 = FStar_Syntax_Util.head_and_args top in
           (match uu____4616 with
            | (unary_op1, uu____4640) ->
                let head1 =
                  let uu____4668 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4668 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____4716;
              FStar_Syntax_Syntax.vars = uu____4717;_},
            a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____4813 = FStar_Syntax_Util.head_and_args top in
           (match uu____4813 with
            | (unary_op1, uu____4837) ->
                let head1 =
                  let uu____4865 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____4865 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____4921;
              FStar_Syntax_Syntax.vars = uu____4922;_},
            (e1, FStar_Pervasives_Native.None)::[])
           ->
           let uu____4960 =
             let uu____4967 =
               let uu____4968 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4968 in
             tc_term uu____4967 e1 in
           (match uu____4960 with
            | (e2, c, g) ->
                let uu____4992 = FStar_Syntax_Util.head_and_args top in
                (match uu____4992 with
                 | (head1, uu____5016) ->
                     let uu____5041 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____5074 =
                       let uu____5075 =
                         let uu____5076 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____5076 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5075 in
                     (uu____5041, uu____5074, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____5077;
              FStar_Syntax_Syntax.vars = uu____5078;_},
            (t, FStar_Pervasives_Native.None)::(r,
                                                FStar_Pervasives_Native.None)::[])
           ->
           let uu____5131 = FStar_Syntax_Util.head_and_args top in
           (match uu____5131 with
            | (head1, uu____5155) ->
                let env' =
                  let uu____5181 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____5181 in
                let uu____5182 = tc_term env' r in
                (match uu____5182 with
                 | (er, uu____5196, gr) ->
                     let uu____5198 = tc_term env1 t in
                     (match uu____5198 with
                      | (t1, tt, gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1 in
                          let uu____5215 =
                            let uu____5216 =
                              let uu____5221 =
                                let uu____5222 =
                                  FStar_Syntax_Syntax.as_arg t1 in
                                let uu____5231 =
                                  let uu____5242 =
                                    FStar_Syntax_Syntax.as_arg r in
                                  [uu____5242] in
                                uu____5222 :: uu____5231 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____5221 in
                            uu____5216 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____5215, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____5277;
              FStar_Syntax_Syntax.vars = uu____5278;_},
            uu____5279)
           ->
           let uu____5304 =
             let uu____5309 =
               let uu____5310 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____5310 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____5309) in
           FStar_Errors.raise_error uu____5304 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____5317;
              FStar_Syntax_Syntax.vars = uu____5318;_},
            uu____5319)
           ->
           let uu____5344 =
             let uu____5349 =
               let uu____5350 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____5350 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____5349) in
           FStar_Errors.raise_error uu____5344 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify);
              FStar_Syntax_Syntax.pos = uu____5357;
              FStar_Syntax_Syntax.vars = uu____5358;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____5401 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____5401 with
             | (env0, uu____5415) ->
                 let uu____5420 = tc_term env0 e1 in
                 (match uu____5420 with
                  | (e2, c, g) ->
                      let uu____5436 = FStar_Syntax_Util.head_and_args top in
                      (match uu____5436 with
                       | (reify_op, uu____5460) ->
                           let u_c =
                             let uu____5486 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ in
                             match uu____5486 with
                             | (uu____5493, c', uu____5495) ->
                                 let uu____5496 =
                                   let uu____5497 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ in
                                   uu____5497.FStar_Syntax_Syntax.n in
                                 (match uu____5496 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____5501 ->
                                      let uu____5502 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____5502 with
                                       | (t, u) ->
                                           let g_opt =
                                             FStar_TypeChecker_Rel.try_teq
                                               true env1
                                               c'.FStar_Syntax_Syntax.res_typ
                                               t in
                                           ((match g_opt with
                                             | FStar_Pervasives_Native.Some
                                                 g' ->
                                                 FStar_TypeChecker_Rel.force_trivial_guard
                                                   env1 g'
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu____5514 =
                                                   let uu____5515 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c' in
                                                   let uu____5516 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ in
                                                   let uu____5517 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____5515 uu____5516
                                                     uu____5517 in
                                                 failwith uu____5514);
                                            u))) in
                           let ef =
                             let uu____5519 =
                               FStar_Syntax_Syntax.lcomp_comp c in
                             FStar_Syntax_Util.comp_effect_name uu____5519 in
                           ((let uu____5523 =
                               let uu____5524 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef in
                               Prims.op_Negation uu____5524 in
                             if uu____5523
                             then
                               let uu____5525 =
                                 let uu____5530 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____5530) in
                               FStar_Errors.raise_error uu____5525
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____5533 =
                                 FStar_Syntax_Syntax.lcomp_comp c in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____5533 u_c in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos in
                             let c1 =
                               let uu____5570 =
                                 FStar_Syntax_Syntax.mk_Total repr in
                               FStar_All.pipe_right uu____5570
                                 FStar_Syntax_Util.lcomp_of_comp in
                             let uu____5571 =
                               comp_check_expected_typ env1 e3 c1 in
                             match uu____5571 with
                             | (e4, c2, g') ->
                                 let uu____5587 =
                                   FStar_TypeChecker_Env.conj_guard g g' in
                                 (e4, c2, uu____5587)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____5589;
              FStar_Syntax_Syntax.vars = uu____5590;_},
            (e1, aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____5634 =
               let uu____5635 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l in
               Prims.op_Negation uu____5635 in
             if uu____5634
             then
               let uu____5636 =
                 let uu____5641 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____5641) in
               FStar_Errors.raise_error uu____5636 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____5643 = FStar_Syntax_Util.head_and_args top in
             match uu____5643 with
             | (reflect_op, uu____5667) ->
                 let uu____5692 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____5692 with
                  | FStar_Pervasives_Native.None ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                      let uu____5731 =
                        FStar_TypeChecker_Env.clear_expected_typ env1 in
                      (match uu____5731 with
                       | (env_no_ex, topt) ->
                           let uu____5750 =
                             let u = FStar_TypeChecker_Env.new_u_univ () in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             let t =
                               let uu____5770 =
                                 let uu____5777 =
                                   let uu____5778 =
                                     let uu____5795 =
                                       let uu____5806 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun in
                                       let uu____5815 =
                                         let uu____5826 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         [uu____5826] in
                                       uu____5806 :: uu____5815 in
                                     (repr, uu____5795) in
                                   FStar_Syntax_Syntax.Tm_app uu____5778 in
                                 FStar_Syntax_Syntax.mk uu____5777 in
                               uu____5770 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____5874 =
                               let uu____5881 =
                                 let uu____5882 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1 in
                                 FStar_All.pipe_right uu____5882
                                   FStar_Pervasives_Native.fst in
                               tc_tot_or_gtot_term uu____5881 t in
                             match uu____5874 with
                             | (t1, uu____5908, g) ->
                                 let uu____5910 =
                                   let uu____5911 =
                                     FStar_Syntax_Subst.compress t1 in
                                   uu____5911.FStar_Syntax_Syntax.n in
                                 (match uu____5910 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____5924,
                                       (res, uu____5926)::(wp, uu____5928)::[])
                                      -> (t1, res, wp, g)
                                  | uu____5985 -> failwith "Impossible") in
                           (match uu____5750 with
                            | (expected_repr_typ, res_typ, wp, g0) ->
                                let uu____6010 =
                                  let uu____6017 =
                                    tc_tot_or_gtot_term env_no_ex e1 in
                                  match uu____6017 with
                                  | (e2, c, g) ->
                                      ((let uu____6034 =
                                          let uu____6035 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____6035 in
                                        if uu____6034
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____6049 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ in
                                        match uu____6049 with
                                        | FStar_Pervasives_Native.None ->
                                            ((let uu____6059 =
                                                let uu____6068 =
                                                  let uu____6075 =
                                                    let uu____6076 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr in
                                                    let uu____6077 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____6076 uu____6077 in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____6075,
                                                    (e2.FStar_Syntax_Syntax.pos)) in
                                                [uu____6068] in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____6059);
                                             (let uu____6090 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0 in
                                              (e2, uu____6090)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____6094 =
                                              let uu____6095 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____6095 in
                                            (e2, uu____6094))) in
                                (match uu____6010 with
                                 | (e2, g) ->
                                     let c =
                                       let uu____6111 =
                                         let uu____6112 =
                                           let uu____6113 =
                                             let uu____6114 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ in
                                             [uu____6114] in
                                           let uu____6115 =
                                             let uu____6126 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____6126] in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____6113;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____6115;
                                             FStar_Syntax_Syntax.flags = []
                                           } in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____6112 in
                                       FStar_All.pipe_right uu____6111
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     let uu____6186 =
                                       comp_check_expected_typ env1 e3 c in
                                     (match uu____6186 with
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
                                          let uu____6209 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g in
                                          (e5, c1, uu____6209))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1, (tau, FStar_Pervasives_Native.None)::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6248 = FStar_Syntax_Util.head_and_args top in
           (match uu____6248 with
            | (head2, args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,
            (uu____6298, FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____6299))::(tau,
                                                          FStar_Pervasives_Native.None)::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6351 = FStar_Syntax_Util.head_and_args top in
           (match uu____6351 with
            | (head2, args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1, args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6426 =
             match args with
             | (tau, FStar_Pervasives_Native.None)::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau, FStar_Pervasives_Native.None)::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____6635 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos in
           (match uu____6426 with
            | (args1, args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1 in
                let t2 = FStar_Syntax_Util.mk_app t1 args2 in tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1, args) ->
           let env0 = env1 in
           let env2 =
             let uu____6752 =
               let uu____6753 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____6753 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____6752 instantiate_both in
           ((let uu____6769 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____6769
             then
               let uu____6770 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____6771 = FStar_Syntax_Print.term_to_string top in
               let uu____6772 =
                 let uu____6773 = FStar_TypeChecker_Env.expected_typ env0 in
                 FStar_All.pipe_right uu____6773
                   (fun uu___341_6779 ->
                      match uu___341_6779 with
                      | FStar_Pervasives_Native.None -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t) in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____6770
                 uu____6771 uu____6772
             else ());
            (let uu____6784 = tc_term (no_inst env2) head1 in
             match uu____6784 with
             | (head2, chead, g_head) ->
                 let uu____6800 =
                   let uu____6807 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____6809 = FStar_Options.lax () in
                         Prims.op_Negation uu____6809))
                       && (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____6807
                   then
                     let uu____6816 =
                       let uu____6823 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____6823 in
                     match uu____6816 with | (e1, c, g) -> (e1, c, g)
                   else
                     (let uu____6836 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____6836) in
                 (match uu____6800 with
                  | (e1, c, g) ->
                      let uu____6848 =
                        let uu____6855 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
                        if uu____6855
                        then
                          let uu____6862 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ in
                          match uu____6862 with
                          | (e2, res_typ, implicits) ->
                              let uu____6878 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ in
                              (e2, uu____6878, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard) in
                      (match uu____6848 with
                       | (e2, c1, implicits) ->
                           ((let uu____6890 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme in
                             if uu____6890
                             then
                               let uu____6891 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____6891
                             else ());
                            (let uu____6893 =
                               comp_check_expected_typ env0 e2 c1 in
                             match uu____6893 with
                             | (e3, c2, g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g' in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits in
                                 ((let uu____6912 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme in
                                   if uu____6912
                                   then
                                     let uu____6913 =
                                       FStar_Syntax_Print.term_to_string e3 in
                                     let uu____6914 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1 in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____6913 uu____6914
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1, eqns) ->
           let uu____6954 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____6954 with
            | (env11, topt) ->
                let env12 = instantiate_both env11 in
                let uu____6974 = tc_term env12 e1 in
                (match uu____6974 with
                 | (e11, c1, g1) ->
                     let uu____6990 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None ->
                           let uu____7004 = FStar_Syntax_Util.type_u () in
                           (match uu____7004 with
                            | (k, uu____7016) ->
                                let uu____7017 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k in
                                (match uu____7017 with
                                 | (res_t, uu____7037, g) ->
                                     let uu____7051 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t in
                                     let uu____7052 =
                                       FStar_TypeChecker_Env.conj_guard g1 g in
                                     (uu____7051, res_t, uu____7052))) in
                     (match uu____6990 with
                      | (env_branches, res_t, g11) ->
                          ((let uu____7063 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____7063
                            then
                              let uu____7064 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____7064
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____7185 =
                              let uu____7190 =
                                FStar_List.fold_right
                                  (fun uu____7269 ->
                                     fun uu____7270 ->
                                       match (uu____7269, uu____7270) with
                                       | ((branch1, f, eff_label, cflags, c,
                                           g),
                                          (caccum, gaccum)) ->
                                           let uu____7504 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____7504)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard) in
                              match uu____7190 with
                              | (cases, g) ->
                                  let uu____7602 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____7602, g) in
                            match uu____7185 with
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
                                           (fun uu____7742 ->
                                              match uu____7742 with
                                              | ((pat, wopt, br), uu____7786,
                                                 eff_label, uu____7788,
                                                 uu____7789, uu____7790) ->
                                                  let uu____7825 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t in
                                                  (pat, wopt, uu____7825))) in
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
                                  let uu____7892 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____7892
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____7897 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____7897 in
                                     let lb =
                                       let uu____7901 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____7901 e11 []
                                         e11.FStar_Syntax_Syntax.pos in
                                     let e2 =
                                       let uu____7907 =
                                         let uu____7914 =
                                           let uu____7915 =
                                             let uu____7928 =
                                               let uu____7931 =
                                                 let uu____7932 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____7932] in
                                               FStar_Syntax_Subst.close
                                                 uu____7931 e_match in
                                             ((false, [lb]), uu____7928) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____7915 in
                                         FStar_Syntax_Syntax.mk uu____7914 in
                                       uu____7907
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____7965 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____7965
                                  then
                                    let uu____7966 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____7967 =
                                      FStar_Syntax_Print.lcomp_to_string cres in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____7966 uu____7967
                                  else ());
                                 (let uu____7969 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches in
                                  (e2, cres, uu____7969))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7970;
               FStar_Syntax_Syntax.lbunivs = uu____7971;
               FStar_Syntax_Syntax.lbtyp = uu____7972;
               FStar_Syntax_Syntax.lbeff = uu____7973;
               FStar_Syntax_Syntax.lbdef = uu____7974;
               FStar_Syntax_Syntax.lbattrs = uu____7975;
               FStar_Syntax_Syntax.lbpos = uu____7976;_}::[]),
            uu____7977)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false, uu____8000), uu____8001) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8016;
               FStar_Syntax_Syntax.lbunivs = uu____8017;
               FStar_Syntax_Syntax.lbtyp = uu____8018;
               FStar_Syntax_Syntax.lbeff = uu____8019;
               FStar_Syntax_Syntax.lbdef = uu____8020;
               FStar_Syntax_Syntax.lbattrs = uu____8021;
               FStar_Syntax_Syntax.lbpos = uu____8022;_}::uu____8023),
            uu____8024)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true, uu____8049), uu____8050) ->
           check_inner_let_rec env1 top)
and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
            FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun head1 ->
    fun env ->
      fun args ->
        fun rng ->
          let uu____8081 =
            match args with
            | (tau, FStar_Pervasives_Native.None)::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____8120))::(tau, FStar_Pervasives_Native.None)::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____8160 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng in
          match uu____8081 with
          | (tau, atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None ->
                    let uu____8191 = FStar_TypeChecker_Env.expected_typ env in
                    (match uu____8191 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None ->
                         let uu____8195 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____8195) in
              let uu____8196 = FStar_TypeChecker_Env.clear_expected_typ env in
              (match uu____8196 with
               | (env', uu____8210) ->
                   let uu____8215 = tc_term env' typ in
                   (match uu____8215 with
                    | (typ1, uu____8229, g1) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                         (let uu____8232 = tc_tactic env' tau in
                          match uu____8232 with
                          | (tau1, uu____8246, g2) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env'
                                 g2;
                               (let t =
                                  env.FStar_TypeChecker_Env.synth_hook env'
                                    typ1
                                    (let uu___355_8251 = tau1 in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (uu___355_8251.FStar_Syntax_Syntax.n);
                                       FStar_Syntax_Syntax.pos = rng;
                                       FStar_Syntax_Syntax.vars =
                                         (uu___355_8251.FStar_Syntax_Syntax.vars)
                                     }) in
                                (let uu____8253 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Tac") in
                                 if uu____8253
                                 then
                                   let uu____8254 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.print1 "Got %s\n" uu____8254
                                 else ());
                                FStar_TypeChecker_Util.check_uvars
                                  tau1.FStar_Syntax_Syntax.pos t;
                                (let uu____8257 =
                                   let uu____8258 =
                                     FStar_Syntax_Syntax.mk_Total typ1 in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.lcomp_of_comp
                                     uu____8258 in
                                 (t, uu____8257,
                                   FStar_TypeChecker_Env.trivial_guard))))))))
and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun tau ->
      let env1 =
        let uu___356_8262 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___356_8262.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___356_8262.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___356_8262.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___356_8262.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___356_8262.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___356_8262.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___356_8262.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___356_8262.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___356_8262.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___356_8262.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___356_8262.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___356_8262.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___356_8262.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___356_8262.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___356_8262.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___356_8262.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___356_8262.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___356_8262.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___356_8262.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___356_8262.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___356_8262.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___356_8262.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___356_8262.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___356_8262.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___356_8262.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___356_8262.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___356_8262.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___356_8262.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___356_8262.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___356_8262.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___356_8262.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___356_8262.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___356_8262.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___356_8262.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___356_8262.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___356_8262.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___356_8262.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___356_8262.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___356_8262.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___356_8262.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___356_8262.FStar_TypeChecker_Env.nbe)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit
and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun topt ->
      match topt with
      | FStar_Pervasives_Native.None ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____8284 = tc_tactic env tactic in
          (match uu____8284 with
           | (tactic1, uu____8298, g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))
and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____8350 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0 in
        match uu____8350 with
        | (e2, t, implicits) ->
            let tc =
              let uu____8371 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____8371
              then FStar_Util.Inl t
              else
                (let uu____8377 =
                   let uu____8378 = FStar_Syntax_Syntax.mk_Total t in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____8378 in
                 FStar_Util.Inr uu____8377) in
            let is_data_ctor uu___342_8386 =
              match uu___342_8386 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____8389) -> true
              | uu____8396 -> false in
            let uu____8399 =
              (is_data_ctor dc) &&
                (let uu____8401 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____8401) in
            if uu____8399
            then
              let uu____8408 =
                let uu____8413 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____8413) in
              let uu____8414 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____8408 uu____8414
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____8431 =
            let uu____8432 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____8432 in
          failwith uu____8431
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____8457 =
            let uu____8462 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
            FStar_Util.Inl uu____8462 in
          value_check_expected_typ env1 e uu____8457
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____8464 =
            let uu____8477 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____8477 with
            | FStar_Pervasives_Native.None ->
                let uu____8492 = FStar_Syntax_Util.type_u () in
                (match uu____8492 with
                 | (k, u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard) in
          (match uu____8464 with
           | (t, uu____8529, g0) ->
               let uu____8543 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____8543 with
                | (e1, uu____8563, g1) ->
                    let uu____8577 =
                      let uu____8578 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____8578
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____8579 = FStar_TypeChecker_Env.conj_guard g0 g1 in
                    (e1, uu____8577, uu____8579)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____8581 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____8590 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____8590)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____8581 with
           | (t, rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___357_8603 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___357_8603.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___357_8603.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____8606 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____8606 with
                 | (e2, t1, implicits) ->
                     let tc =
                       let uu____8627 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____8627
                       then FStar_Util.Inl t1
                       else
                         (let uu____8633 =
                            let uu____8634 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____8634 in
                          FStar_Util.Inr uu____8633) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8636;
             FStar_Syntax_Syntax.vars = uu____8637;_},
           uu____8638)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8643 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8643
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8651 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8651
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8659;
             FStar_Syntax_Syntax.vars = uu____8660;_},
           us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____8669 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____8669 with
           | ((us', t), range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____8692 =
                     let uu____8697 =
                       let uu____8698 = FStar_Syntax_Print.fv_to_string fv in
                       let uu____8699 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____8700 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____8698 uu____8699 uu____8700 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____8697) in
                   let uu____8701 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____8692 uu____8701)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____8717 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8721 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8721 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8723 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____8723 with
           | ((us, t), range) ->
               ((let uu____8746 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____8746
                 then
                   let uu____8747 =
                     let uu____8748 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____8748 in
                   let uu____8749 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____8750 = FStar_Range.string_of_range range in
                   let uu____8751 = FStar_Range.string_of_use_range range in
                   let uu____8752 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____8747 uu____8749 uu____8750 uu____8751 uu____8752
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8757 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8757 us in
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
          let uu____8785 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____8785 with
           | (bs1, c1) ->
               let env0 = env1 in
               let uu____8799 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8799 with
                | (env2, uu____8813) ->
                    let uu____8818 = tc_binders env2 bs1 in
                    (match uu____8818 with
                     | (bs2, env3, g, us) ->
                         let uu____8837 = tc_comp env3 c1 in
                         (match uu____8837 with
                          | (c2, uc, f) ->
                              let e1 =
                                let uu___358_8856 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___358_8856.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___358_8856.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____8867 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____8867 in
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
          let uu____8883 =
            let uu____8888 =
              let uu____8889 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8889] in
            FStar_Syntax_Subst.open_term uu____8888 phi in
          (match uu____8883 with
           | (x1, phi1) ->
               let env0 = env1 in
               let uu____8917 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8917 with
                | (env2, uu____8931) ->
                    let uu____8936 =
                      let uu____8951 = FStar_List.hd x1 in
                      tc_binder env2 uu____8951 in
                    (match uu____8936 with
                     | (x2, env3, f1, u) ->
                         ((let uu____8987 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____8987
                           then
                             let uu____8988 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____8989 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8990 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____8988 uu____8989 uu____8990
                           else ());
                          (let uu____8994 = FStar_Syntax_Util.type_u () in
                           match uu____8994 with
                           | (t_phi, uu____9006) ->
                               let uu____9007 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____9007 with
                                | (phi2, uu____9021, f2) ->
                                    let e1 =
                                      let uu___359_9026 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___359_9026.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___359_9026.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____9035 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____9035 in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____9063) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____9090 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____9090
            then
              let uu____9091 =
                FStar_Syntax_Print.term_to_string
                  (let uu___360_9094 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___360_9094.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_9094.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____9091
            else ());
           (let uu____9108 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____9108 with | (bs2, body1) -> tc_abs env1 top bs2 body1))
      | uu____9121 ->
          let uu____9122 =
            let uu____9123 = FStar_Syntax_Print.term_to_string top in
            let uu____9124 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____9123
              uu____9124 in
          failwith uu____9122
and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun r ->
      fun c ->
        match c with
        | FStar_Const.Const_unit -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____9134 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____9135, FStar_Pervasives_Native.None) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____9146, FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____9162 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____9167 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____9168 ->
            let uu____9170 =
              let uu____9175 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____9175 FStar_Util.must in
            FStar_All.pipe_right uu____9170 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____9200 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of ->
            let uu____9201 =
              let uu____9206 =
                let uu____9207 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9207 in
              (FStar_Errors.Fatal_IllTyped, uu____9206) in
            FStar_Errors.raise_error uu____9201 r
        | FStar_Const.Const_set_range_of ->
            let uu____9208 =
              let uu____9213 =
                let uu____9214 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9214 in
              (FStar_Errors.Fatal_IllTyped, uu____9213) in
            FStar_Errors.raise_error uu____9208 r
        | FStar_Const.Const_reify ->
            let uu____9215 =
              let uu____9220 =
                let uu____9221 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9221 in
              (FStar_Errors.Fatal_IllTyped, uu____9220) in
            FStar_Errors.raise_error uu____9215 r
        | FStar_Const.Const_reflect uu____9222 ->
            let uu____9223 =
              let uu____9228 =
                let uu____9229 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9229 in
              (FStar_Errors.Fatal_IllTyped, uu____9228) in
            FStar_Errors.raise_error uu____9223 r
        | uu____9230 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r
and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp, FStar_Syntax_Syntax.universe,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun c ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uu____9247) ->
          let uu____9256 = FStar_Syntax_Util.type_u () in
          (match uu____9256 with
           | (k, u) ->
               let uu____9269 = tc_check_tot_or_gtot_term env t k in
               (match uu____9269 with
                | (t1, uu____9283, g) ->
                    let uu____9285 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____9285, u, g)))
      | FStar_Syntax_Syntax.GTotal (t, uu____9287) ->
          let uu____9296 = FStar_Syntax_Util.type_u () in
          (match uu____9296 with
           | (k, u) ->
               let uu____9309 = tc_check_tot_or_gtot_term env t k in
               (match uu____9309 with
                | (t1, uu____9323, g) ->
                    let uu____9325 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____9325, u, g)))
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
            let uu____9335 =
              let uu____9340 =
                let uu____9341 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____9341 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____9340 in
            uu____9335 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____9360 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____9360 with
           | (tc1, uu____9374, f) ->
               let uu____9376 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____9376 with
                | (head3, args) ->
                    let comp_univs =
                      let uu____9426 =
                        let uu____9427 = FStar_Syntax_Subst.compress head3 in
                        uu____9427.FStar_Syntax_Syntax.n in
                      match uu____9426 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____9430, us) -> us
                      | uu____9436 -> [] in
                    let uu____9437 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____9437 with
                     | (uu____9460, args1) ->
                         let uu____9486 =
                           let uu____9509 = FStar_List.hd args1 in
                           let uu____9526 = FStar_List.tl args1 in
                           (uu____9509, uu____9526) in
                         (match uu____9486 with
                          | (res, args2) ->
                              let uu____9607 =
                                let uu____9616 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___343_9644 ->
                                          match uu___343_9644 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____9652 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____9652 with
                                               | (env1, uu____9664) ->
                                                   let uu____9669 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____9669 with
                                                    | (e1, uu____9681, g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard))) in
                                FStar_All.pipe_right uu____9616
                                  FStar_List.unzip in
                              (match uu____9607 with
                               | (flags1, guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___361_9722 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___361_9722.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___361_9722.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____9728 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____9728 with
                                     | FStar_Pervasives_Native.None -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____9732 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards in
                                   (c2, u_c, uu____9732))))))
and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____9742 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____9743 -> u2
        | FStar_Syntax_Syntax.U_zero -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____9753 = aux u3 in FStar_Syntax_Syntax.U_succ uu____9753
        | FStar_Syntax_Syntax.U_max us ->
            let uu____9757 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____9757
        | FStar_Syntax_Syntax.U_name x ->
            let uu____9761 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x) in
            if uu____9761
            then u2
            else
              (let uu____9763 =
                 let uu____9764 =
                   let uu____9765 = FStar_Syntax_Print.univ_to_string u2 in
                   Prims.strcat uu____9765 " not found" in
                 Prims.strcat "Universe variable " uu____9764 in
               failwith uu____9763) in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown ->
             let uu____9767 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____9767 FStar_Pervasives_Native.snd
         | uu____9776 -> aux u)
and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
            FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun top ->
      fun bs ->
        fun body ->
          let fail1 msg t =
            let uu____9805 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____9805 top.FStar_Syntax_Syntax.pos in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____9893 bs2 bs_expected1 =
              match uu____9893 with
              | (env2, subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([], []) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1, imp)::bs3, (hd_expected, imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None,
                            FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____10063)) ->
                             let uu____10068 =
                               let uu____10073 =
                                 let uu____10074 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10074 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10073) in
                             let uu____10075 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____10068 uu____10075
                         | (FStar_Pervasives_Native.None,
                            FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta uu____10076)) ->
                             let uu____10083 =
                               let uu____10088 =
                                 let uu____10089 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10089 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10088) in
                             let uu____10090 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____10083 uu____10090
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____10091),
                            FStar_Pervasives_Native.None) ->
                             let uu____10096 =
                               let uu____10101 =
                                 let uu____10102 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10102 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10101) in
                             let uu____10103 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____10096 uu____10103
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta uu____10104),
                            FStar_Pervasives_Native.None) ->
                             let uu____10111 =
                               let uu____10116 =
                                 let uu____10117 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10117 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10116) in
                             let uu____10118 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____10111 uu____10118
                         | uu____10119 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____10129 =
                           let uu____10136 =
                             let uu____10137 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____10137.FStar_Syntax_Syntax.n in
                           match uu____10136 with
                           | FStar_Syntax_Syntax.Tm_unknown ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10148 ->
                               ((let uu____10150 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____10150
                                 then
                                   let uu____10151 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____10151
                                 else ());
                                (let uu____10153 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____10153 with
                                 | (t, uu____10167, g1_env) ->
                                     let g2_env =
                                       let uu____10170 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t in
                                       if uu____10170
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____10172 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t in
                                          match uu____10172 with
                                          | FStar_Pervasives_Native.None ->
                                              let uu____10175 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t in
                                              let uu____10180 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_Errors.raise_error
                                                uu____10175 uu____10180
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____10182 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____10182
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env) in
                                     let uu____10183 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env in
                                     (t, uu____10183))) in
                         match uu____10129 with
                         | (t, g_env) ->
                             let hd2 =
                               let uu___362_10209 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___362_10209.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___362_10209.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env_b = push_binding env2 b in
                             let subst2 =
                               let uu____10232 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____10232 in
                             let uu____10235 =
                               aux (env_b, subst2) bs3 bs_expected2 in
                             (match uu____10235 with
                              | (env_bs, bs4, rest, g'_env_b, subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b in
                                  let uu____10300 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env in
                                  (env_bs, (b :: bs4), rest, uu____10300,
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
                  | uu____10472 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____10481 = tc_binders env1 bs in
                  match uu____10481 with
                  | (bs1, envbody, g_env, uu____10511) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____10565 =
                    let uu____10566 = FStar_Syntax_Subst.compress t2 in
                    uu____10566.FStar_Syntax_Syntax.n in
                  match uu____10565 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____10599 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10619 -> failwith "Impossible");
                       (let uu____10628 = tc_binders env1 bs in
                        match uu____10628 with
                        | (bs1, envbody, g_env, uu____10670) ->
                            let uu____10671 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____10671 with
                             | (envbody1, uu____10709) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____10730;
                         FStar_Syntax_Syntax.pos = uu____10731;
                         FStar_Syntax_Syntax.vars = uu____10732;_},
                       uu____10733)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10777 -> failwith "Impossible");
                       (let uu____10786 = tc_binders env1 bs in
                        match uu____10786 with
                        | (bs1, envbody, g_env, uu____10828) ->
                            let uu____10829 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____10829 with
                             | (envbody1, uu____10867) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____10889) ->
                      let uu____10894 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____10894 with
                       | (uu____10955, bs1, bs', copt, env_body, body2,
                          g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) ->
                      let uu____11032 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____11032 with
                       | (bs_expected1, c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____11177 c_expected2
                               body3 =
                               match uu____11177 with
                               | (env_bs, bs2, more, guard_env, subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None ->
                                        let uu____11291 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env_bs, bs2, guard_env, uu____11291,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____11308 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____11308 in
                                        let uu____11309 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env_bs, bs2, guard_env, uu____11309,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____11326 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____11326
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
                                               let uu____11390 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____11390 with
                                                | (bs_expected4, c_expected4)
                                                    ->
                                                    let uu____11417 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4 in
                                                    (match uu____11417 with
                                                     | (env_bs_bs', bs',
                                                        more1, guard'_env_bs,
                                                        subst2) ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs in
                                                         let uu____11472 =
                                                           let uu____11499 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____11499,
                                                             subst2) in
                                                         handle_more
                                                           uu____11472
                                                           c_expected4 body3))
                                           | uu____11522 ->
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
                             let uu____11550 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____11550 c_expected1 body2 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___363_11613 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___363_11613.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___363_11613.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___363_11613.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___363_11613.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___363_11613.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___363_11613.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___363_11613.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___363_11613.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___363_11613.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___363_11613.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___363_11613.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___363_11613.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___363_11613.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___363_11613.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___363_11613.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___363_11613.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___363_11613.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___363_11613.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___363_11613.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___363_11613.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___363_11613.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___363_11613.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___363_11613.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___363_11613.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___363_11613.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___363_11613.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___363_11613.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___363_11613.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___363_11613.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___363_11613.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___363_11613.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___363_11613.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___363_11613.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___363_11613.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___363_11613.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___363_11613.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___363_11613.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___363_11613.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___363_11613.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___363_11613.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___363_11613.FStar_TypeChecker_Env.nbe)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____11671 ->
                                     fun uu____11672 ->
                                       match (uu____11671, uu____11672) with
                                       | ((env2, letrec_binders),
                                          (l, t3, u_names)) ->
                                           let uu____11754 =
                                             let uu____11761 =
                                               let uu____11762 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____11762
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____11761 t3 in
                                           (match uu____11754 with
                                            | (t4, uu____11784, uu____11785)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____11797 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___364_11800
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___364_11800.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___364_11800.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____11797 ::
                                                        letrec_binders
                                                  | uu____11801 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____11810 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1 in
                           (match uu____11810 with
                            | (envbody, bs1, g_env, c, body2) ->
                                let uu____11886 = mk_letrec_env envbody bs1 c in
                                (match uu____11886 with
                                 | (envbody1, letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g_env))))
                  | uu____11946 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____11977 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____11977
                      else
                        (let uu____11979 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____11979 with
                         | (uu____12028, bs1, uu____12030, c_opt, envbody,
                            body2, g_env) ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____12060 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____12060 with
          | (env1, topt) ->
              ((let uu____12080 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____12080
                then
                  let uu____12081 =
                    match topt with
                    | FStar_Pervasives_Native.None -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____12081
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____12085 = expected_function_typ1 env1 topt body in
                match uu____12085 with
                | (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1,
                   g_env) ->
                    ((let uu____12126 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC") in
                      if uu____12126
                      then
                        let uu____12127 =
                          FStar_Syntax_Print.binders_to_string ", " bs1 in
                        let uu____12128 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____12127 uu____12128
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos in
                      let uu____12131 =
                        let should_check_expected_effect =
                          let uu____12143 =
                            let uu____12150 =
                              let uu____12151 =
                                FStar_Syntax_Subst.compress body1 in
                              uu____12151.FStar_Syntax_Syntax.n in
                            (c_opt, uu____12150) in
                          match uu____12143 with
                          | (FStar_Pervasives_Native.None,
                             FStar_Syntax_Syntax.Tm_ascribed
                             (uu____12156,
                              (FStar_Util.Inr expected_c, uu____12158),
                              uu____12159)) -> false
                          | uu____12208 -> true in
                        let uu____12215 =
                          tc_term
                            (let uu___365_12224 = envbody1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___365_12224.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___365_12224.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___365_12224.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___365_12224.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___365_12224.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___365_12224.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___365_12224.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___365_12224.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___365_12224.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___365_12224.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___365_12224.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___365_12224.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___365_12224.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___365_12224.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___365_12224.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___365_12224.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___365_12224.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___365_12224.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___365_12224.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___365_12224.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___365_12224.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___365_12224.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___365_12224.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___365_12224.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___365_12224.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___365_12224.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___365_12224.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___365_12224.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___365_12224.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___365_12224.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___365_12224.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___365_12224.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___365_12224.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___365_12224.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___365_12224.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___365_12224.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___365_12224.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___365_12224.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___365_12224.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___365_12224.FStar_TypeChecker_Env.nbe)
                             }) body1 in
                        match uu____12215 with
                        | (body2, cbody, guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body in
                            if should_check_expected_effect
                            then
                              let uu____12249 =
                                let uu____12256 =
                                  let uu____12261 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody in
                                  (body2, uu____12261) in
                                check_expected_effect
                                  (let uu___366_12264 = envbody1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___366_12264.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___366_12264.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___366_12264.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___366_12264.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___366_12264.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___366_12264.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___366_12264.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___366_12264.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___366_12264.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___366_12264.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___366_12264.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___366_12264.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___366_12264.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___366_12264.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___366_12264.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___366_12264.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___366_12264.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___366_12264.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___366_12264.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___366_12264.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___366_12264.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___366_12264.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___366_12264.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___366_12264.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___366_12264.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___366_12264.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___366_12264.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___366_12264.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___366_12264.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___366_12264.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___366_12264.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___366_12264.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___366_12264.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___366_12264.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___366_12264.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___366_12264.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___366_12264.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___366_12264.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___366_12264.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___366_12264.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___366_12264.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____12256 in
                              (match uu____12249 with
                               | (body3, cbody1, guard) ->
                                   let uu____12278 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard in
                                   (body3, cbody1, uu____12278))
                            else
                              (let uu____12284 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody in
                               (body2, uu____12284, guard_body1)) in
                      match uu____12131 with
                      | (body2, cbody, guard_body) ->
                          let guard =
                            let uu____12309 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____12311 =
                                   FStar_TypeChecker_Env.should_verify env1 in
                                 Prims.op_Negation uu____12311) in
                            if uu____12309
                            then
                              let uu____12312 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env in
                              let uu____12313 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body in
                              FStar_TypeChecker_Env.conj_guard uu____12312
                                uu____12313
                            else
                              (let guard =
                                 let uu____12316 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____12316 in
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
                          let uu____12330 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____12351
                                     -> (e, t1, guard1)
                                 | uu____12366 ->
                                     let uu____12367 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1 in
                                     (match uu____12367 with
                                      | (e1, guard') ->
                                          let uu____12380 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard' in
                                          (e1, t1, uu____12380)))
                            | FStar_Pervasives_Native.None ->
                                (e, tfun_computed, guard1) in
                          (match uu____12330 with
                           | (e1, tfun, guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun in
                               let uu____12391 =
                                 let uu____12396 =
                                   FStar_Syntax_Util.lcomp_of_comp c in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____12396 guard2 in
                               (match uu____12391 with
                                | (c1, g) -> (e1, c1, g)))))))
and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
                FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
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
              (let uu____12444 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____12444
               then
                 let uu____12445 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____12446 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____12445
                   uu____12446
               else ());
              (let monadic_application uu____12523 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____12523 with
                 | (head2, chead1, ghead1, cres) ->
                     let uu____12590 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     (match uu____12590 with
                      | (rt, g0) ->
                          let cres1 =
                            let uu___367_12604 = cres in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___367_12604.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___367_12604.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___367_12604.FStar_Syntax_Syntax.comp_thunk)
                            } in
                          let uu____12605 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____12621 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____12621 in
                                (cres1, g)
                            | uu____12622 ->
                                let g =
                                  let uu____12632 =
                                    let uu____12633 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard in
                                    FStar_All.pipe_right uu____12633
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env) in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____12632 in
                                let uu____12634 =
                                  let uu____12635 =
                                    let uu____12636 =
                                      let uu____12637 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1 in
                                      FStar_Syntax_Util.arrow bs uu____12637 in
                                    FStar_Syntax_Syntax.mk_Total uu____12636 in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____12635 in
                                (uu____12634, g) in
                          (match uu____12605 with
                           | (cres2, guard1) ->
                               ((let uu____12649 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low in
                                 if uu____12649
                                 then
                                   let uu____12650 =
                                     FStar_Syntax_Print.lcomp_to_string cres2 in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____12650
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____12666 ->
                                             match uu____12666 with
                                             | (uu____12675, uu____12676, lc)
                                                 ->
                                                 (let uu____12684 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc in
                                                  Prims.op_Negation
                                                    uu____12684)
                                                   ||
                                                   (FStar_TypeChecker_Util.should_not_inline_lc
                                                      lc)) arg_comps_rev) in
                                   let term =
                                     FStar_Syntax_Syntax.mk_Tm_app head2
                                       (FStar_List.rev arg_rets_rev)
                                       FStar_Pervasives_Native.None
                                       head2.FStar_Syntax_Syntax.pos in
                                   let uu____12696 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful in
                                   if uu____12696
                                   then
                                     ((let uu____12698 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____12698
                                       then
                                         let uu____12699 =
                                           FStar_Syntax_Print.term_to_string
                                             term in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____12699
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____12703 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____12703
                                       then
                                         let uu____12704 =
                                           FStar_Syntax_Print.term_to_string
                                             term in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____12704
                                       else ());
                                      cres2) in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c ->
                                        fun uu____12732 ->
                                          match uu____12732 with
                                          | ((e, q), x, c) ->
                                              ((let uu____12774 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme in
                                                if uu____12774
                                                then
                                                  let uu____12775 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                        -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1 in
                                                  let uu____12777 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e in
                                                  let uu____12778 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____12775 uu____12777
                                                    uu____12778
                                                else ());
                                               (let uu____12780 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c in
                                                if uu____12780
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
                                   (let uu____12788 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme in
                                    if uu____12788
                                    then
                                      let uu____12789 =
                                        FStar_Syntax_Print.term_to_string
                                          head2 in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____12789
                                    else ());
                                   (let uu____12791 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1 in
                                    if uu____12791
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
                                   let uu____12799 =
                                     let uu____12800 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____12800.FStar_Syntax_Syntax.n in
                                   match uu____12799 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____12804 -> false in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1 ->
                                            fun uu____12825 ->
                                              match uu____12825 with
                                              | (arg, uu____12839,
                                                 uu____12840) -> arg :: args1)
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
                                     (let uu____12850 =
                                        let map_fun uu____12912 =
                                          match uu____12912 with
                                          | ((e, q), uu____12949, c) ->
                                              ((let uu____12966 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme in
                                                if uu____12966
                                                then
                                                  let uu____12967 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e in
                                                  let uu____12968 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____12967 uu____12968
                                                else ());
                                               (let uu____12970 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c in
                                                if uu____12970
                                                then
                                                  ((let uu____12992 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____12992
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  ((let uu____13022 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme in
                                                    if uu____13022
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
                                                    let uu____13026 =
                                                      let uu____13033 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x in
                                                      (uu____13033, q) in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____13026))))) in
                                        let uu____13060 =
                                          let uu____13089 =
                                            let uu____13116 =
                                              let uu____13127 =
                                                let uu____13136 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2 in
                                                (uu____13136,
                                                  FStar_Pervasives_Native.None,
                                                  chead1) in
                                              uu____13127 :: arg_comps_rev in
                                            FStar_List.map map_fun
                                              uu____13116 in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____13089 in
                                        match uu____13060 with
                                        | (lifted_args, reverse_args) ->
                                            let uu____13325 =
                                              let uu____13326 =
                                                FStar_List.hd reverse_args in
                                              FStar_Pervasives_Native.fst
                                                uu____13326 in
                                            let uu____13341 =
                                              let uu____13342 =
                                                FStar_List.tl reverse_args in
                                              FStar_List.rev uu____13342 in
                                            (lifted_args, uu____13325,
                                              uu____13341) in
                                      match uu____12850 with
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
                                          let bind_lifted_args e
                                            uu___344_13447 =
                                            match uu___344_13447 with
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
                                                  let uu____13508 =
                                                    let uu____13515 =
                                                      let uu____13516 =
                                                        let uu____13529 =
                                                          let uu____13532 =
                                                            let uu____13533 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x in
                                                            [uu____13533] in
                                                          FStar_Syntax_Subst.close
                                                            uu____13532 e in
                                                        ((false, [lb]),
                                                          uu____13529) in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____13516 in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____13515 in
                                                  uu____13508
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
                                 let uu____13585 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1 in
                                 match uu____13585 with
                                 | (comp3, g) ->
                                     ((let uu____13602 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme in
                                       if uu____13602
                                       then
                                         let uu____13603 =
                                           FStar_Syntax_Print.term_to_string
                                             app in
                                         let uu____13604 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3 in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____13603 uu____13604
                                       else ());
                                      (app, comp3, g)))))) in
               let rec tc_args head_info uu____13682 bs args1 =
                 match uu____13682 with
                 | (subst1, outargs, arg_rets, g, fvs) ->
                     (match (bs, args1) with
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13821))::rest,
                         (uu____13823, FStar_Pervasives_Native.None)::uu____13824)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____13884 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          (match uu____13884 with
                           | (t1, g_ex) ->
                               let uu____13897 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1 in
                               (match uu____13897 with
                                | (varg, uu____13917, implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1 in
                                    let arg =
                                      let uu____13945 =
                                        FStar_Syntax_Syntax.as_implicit true in
                                      (varg, uu____13945) in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits in
                                    let uu____13953 =
                                      let uu____13988 =
                                        let uu____13999 =
                                          let uu____14008 =
                                            let uu____14009 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_All.pipe_right uu____14009
                                              FStar_Syntax_Util.lcomp_of_comp in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____14008) in
                                        uu____13999 :: outargs in
                                      (subst2, uu____13988, (arg ::
                                        arg_rets), guard, fvs) in
                                    tc_args head_info uu____13953 rest args1))
                      | ((x, FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,
                         (uu____14055, FStar_Pervasives_Native.None)::uu____14056)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau in
                          let uu____14118 = tc_tactic env tau1 in
                          (match uu____14118 with
                           | (tau2, uu____14132, g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____14135 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t in
                               (match uu____14135 with
                                | (t1, g_ex) ->
                                    let uu____14148 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1 in
                                    (match uu____14148 with
                                     | (varg, uu____14168, implicits) ->
                                         let mark_meta_implicits tau3 g1 =
                                           let uu___368_14193 = g1 in
                                           let uu____14194 =
                                             FStar_List.map
                                               (fun imp ->
                                                  let uu___369_14200 = imp in
                                                  {
                                                    FStar_TypeChecker_Env.imp_reason
                                                      =
                                                      (uu___369_14200.FStar_TypeChecker_Env.imp_reason);
                                                    FStar_TypeChecker_Env.imp_uvar
                                                      =
                                                      (uu___369_14200.FStar_TypeChecker_Env.imp_uvar);
                                                    FStar_TypeChecker_Env.imp_tm
                                                      =
                                                      (uu___369_14200.FStar_TypeChecker_Env.imp_tm);
                                                    FStar_TypeChecker_Env.imp_range
                                                      =
                                                      (uu___369_14200.FStar_TypeChecker_Env.imp_range);
                                                    FStar_TypeChecker_Env.imp_meta
                                                      =
                                                      (FStar_Pervasives_Native.Some
                                                         (env, tau3))
                                                  })
                                               g1.FStar_TypeChecker_Env.implicits in
                                           {
                                             FStar_TypeChecker_Env.guard_f =
                                               (uu___368_14193.FStar_TypeChecker_Env.guard_f);
                                             FStar_TypeChecker_Env.deferred =
                                               (uu___368_14193.FStar_TypeChecker_Env.deferred);
                                             FStar_TypeChecker_Env.univ_ineqs
                                               =
                                               (uu___368_14193.FStar_TypeChecker_Env.univ_ineqs);
                                             FStar_TypeChecker_Env.implicits
                                               = uu____14194
                                           } in
                                         let implicits1 =
                                           mark_meta_implicits tau2 implicits in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1 in
                                         let arg =
                                           let uu____14220 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true in
                                           (varg, uu____14220) in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits1 in
                                         let uu____14228 =
                                           let uu____14263 =
                                             let uu____14274 =
                                               let uu____14283 =
                                                 let uu____14284 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1 in
                                                 FStar_All.pipe_right
                                                   uu____14284
                                                   FStar_Syntax_Util.lcomp_of_comp in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____14283) in
                                             uu____14274 :: outargs in
                                           (subst2, uu____14263, (arg ::
                                             arg_rets), guard, fvs) in
                                         tc_args head_info uu____14228 rest
                                           args1)))
                      | ((x, aqual)::rest, (e, aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____14400, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____14401)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____14410),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14411)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14418),
                               FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14419)) ->
                                ()
                            | (FStar_Pervasives_Native.None,
                               FStar_Pervasives_Native.None) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality),
                               FStar_Pervasives_Native.None) -> ()
                            | uu____14432 ->
                                let uu____14441 =
                                  let uu____14446 =
                                    let uu____14447 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual in
                                    let uu____14448 =
                                      FStar_Syntax_Print.aqual_to_string aq in
                                    let uu____14449 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____14450 =
                                      FStar_Syntax_Print.term_to_string e in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____14447 uu____14448 uu____14449
                                      uu____14450 in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____14446) in
                                FStar_Errors.raise_error uu____14441
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual in
                            let x1 =
                              let uu___370_14454 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___370_14454.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___370_14454.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____14456 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____14456
                             then
                               let uu____14457 =
                                 FStar_Syntax_Print.bv_to_string x1 in
                               let uu____14458 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort in
                               let uu____14459 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____14460 =
                                 FStar_Syntax_Print.subst_to_string subst1 in
                               let uu____14461 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____14457 uu____14458 uu____14459
                                 uu____14460 uu____14461
                             else ());
                            (let uu____14463 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             match uu____14463 with
                             | (targ1, g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1 in
                                 let env2 =
                                   let uu___371_14478 = env1 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___371_14478.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___371_14478.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___371_14478.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___371_14478.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___371_14478.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___371_14478.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___371_14478.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___371_14478.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___371_14478.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___371_14478.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___371_14478.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___371_14478.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___371_14478.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___371_14478.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___371_14478.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___371_14478.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___371_14478.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___371_14478.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___371_14478.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___371_14478.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___371_14478.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___371_14478.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___371_14478.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___371_14478.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___371_14478.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___371_14478.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___371_14478.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___371_14478.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___371_14478.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___371_14478.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___371_14478.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___371_14478.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___371_14478.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___371_14478.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___371_14478.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___371_14478.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___371_14478.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___371_14478.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___371_14478.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___371_14478.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___371_14478.FStar_TypeChecker_Env.nbe)
                                   } in
                                 ((let uu____14480 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High in
                                   if uu____14480
                                   then
                                     let uu____14481 =
                                       FStar_Syntax_Print.tag_of_term e in
                                     let uu____14482 =
                                       FStar_Syntax_Print.term_to_string e in
                                     let uu____14483 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1 in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____14481 uu____14482 uu____14483
                                   else ());
                                  (let uu____14485 = tc_term env2 e in
                                   match uu____14485 with
                                   | (e1, c, g_e) ->
                                       let g1 =
                                         let uu____14502 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____14502 in
                                       let arg = (e1, aq) in
                                       let xterm =
                                         let uu____14525 =
                                           let uu____14528 =
                                             let uu____14537 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14537 in
                                           FStar_Pervasives_Native.fst
                                             uu____14528 in
                                         (uu____14525, aq) in
                                       let uu____14546 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name) in
                                       if uu____14546
                                       then
                                         let subst2 =
                                           let uu____14554 = FStar_List.hd bs in
                                           maybe_extend_subst subst1
                                             uu____14554 e1 in
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
                      | (uu____14652, []) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([], arg::uu____14688) ->
                          let uu____14739 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____14739 with
                           | (head2, chead1, ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____14791 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____14791
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1, cres')
                                     ->
                                     let uu____14822 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____14822 with
                                      | (bs2, cres'1) ->
                                          let head_info1 =
                                            let uu____14844 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1 in
                                            (head2, chead1, ghead2,
                                              uu____14844) in
                                          ((let uu____14846 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____14846
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
                                 | uu____14888 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2 in
                                       let uu____14896 =
                                         let uu____14897 =
                                           FStar_Syntax_Subst.compress tres3 in
                                         uu____14897.FStar_Syntax_Syntax.n in
                                       match uu____14896 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____14900;
                                              FStar_Syntax_Syntax.index =
                                                uu____14901;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},
                                            uu____14903)
                                           -> norm_tres tres4
                                       | uu____14910 -> tres3 in
                                     let uu____14911 = norm_tres tres1 in
                                     aux true solve ghead2 uu____14911
                                 | uu____14912 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2 in
                                     aux norm1 true ghead3 tres1
                                 | uu____14914 ->
                                     let uu____14915 =
                                       let uu____14920 =
                                         let uu____14921 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead in
                                         let uu____14922 =
                                           FStar_Util.string_of_int n_args in
                                         let uu____14929 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1 in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____14921 uu____14922
                                           uu____14929 in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____14920) in
                                     let uu____14930 =
                                       FStar_Syntax_Syntax.argpos arg in
                                     FStar_Errors.raise_error uu____14915
                                       uu____14930 in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf guard =
                 let uu____14958 =
                   let uu____14959 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____14959.FStar_Syntax_Syntax.n in
                 match uu____14958 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____14968 ->
                     let uu____14981 =
                       FStar_List.fold_right
                         (fun uu____15012 ->
                            fun uu____15013 ->
                              match uu____15013 with
                              | (bs, guard1) ->
                                  let uu____15040 =
                                    let uu____15053 =
                                      let uu____15054 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____15054
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____15053 in
                                  (match uu____15040 with
                                   | (t, uu____15070, g) ->
                                       let uu____15084 =
                                         let uu____15087 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____15087 :: bs in
                                       let uu____15088 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____15084, uu____15088))) args
                         ([], guard) in
                     (match uu____14981 with
                      | (bs, guard1) ->
                          let uu____15105 =
                            let uu____15112 =
                              let uu____15125 =
                                let uu____15126 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____15126
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____15125 in
                            match uu____15112 with
                            | (t, uu____15142, g) ->
                                let uu____15156 = FStar_Options.ml_ish () in
                                if uu____15156
                                then
                                  let uu____15163 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____15166 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____15163, uu____15166)
                                else
                                  (let uu____15170 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____15173 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____15170, uu____15173)) in
                          (match uu____15105 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____15192 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____15192
                                 then
                                   let uu____15193 =
                                     FStar_Syntax_Print.term_to_string head1 in
                                   let uu____15194 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____15195 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____15193 uu____15194 uu____15195
                                 else ());
                                (let g =
                                   let uu____15198 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____15198 in
                                 let uu____15199 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____15199))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____15200;
                        FStar_Syntax_Syntax.pos = uu____15201;
                        FStar_Syntax_Syntax.vars = uu____15202;_},
                      uu____15203)
                     ->
                     let uu____15240 =
                       FStar_List.fold_right
                         (fun uu____15271 ->
                            fun uu____15272 ->
                              match uu____15272 with
                              | (bs, guard1) ->
                                  let uu____15299 =
                                    let uu____15312 =
                                      let uu____15313 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____15313
                                        FStar_Pervasives_Native.fst in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____15312 in
                                  (match uu____15299 with
                                   | (t, uu____15329, g) ->
                                       let uu____15343 =
                                         let uu____15346 =
                                           FStar_Syntax_Syntax.null_binder t in
                                         uu____15346 :: bs in
                                       let uu____15347 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1 in
                                       (uu____15343, uu____15347))) args
                         ([], guard) in
                     (match uu____15240 with
                      | (bs, guard1) ->
                          let uu____15364 =
                            let uu____15371 =
                              let uu____15384 =
                                let uu____15385 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____15385
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____15384 in
                            match uu____15371 with
                            | (t, uu____15401, g) ->
                                let uu____15415 = FStar_Options.ml_ish () in
                                if uu____15415
                                then
                                  let uu____15422 =
                                    FStar_Syntax_Util.ml_comp t r in
                                  let uu____15425 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g in
                                  (uu____15422, uu____15425)
                                else
                                  (let uu____15429 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   let uu____15432 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g in
                                   (uu____15429, uu____15432)) in
                          (match uu____15364 with
                           | (cres, guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres in
                               ((let uu____15451 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____15451
                                 then
                                   let uu____15452 =
                                     FStar_Syntax_Print.term_to_string head1 in
                                   let uu____15453 =
                                     FStar_Syntax_Print.term_to_string tf in
                                   let uu____15454 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____15452 uu____15453 uu____15454
                                 else ());
                                (let g =
                                   let uu____15457 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____15457 in
                                 let uu____15458 =
                                   FStar_TypeChecker_Env.conj_guard g guard2 in
                                 check_function_app bs_cres uu____15458))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                     let uu____15481 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____15481 with
                      | (bs1, c1) ->
                          let head_info =
                            let uu____15503 =
                              FStar_Syntax_Util.lcomp_of_comp c1 in
                            (head1, chead, ghead, uu____15503) in
                          ((let uu____15505 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme in
                            if uu____15505
                            then
                              let uu____15506 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____15507 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____15508 =
                                FStar_Syntax_Print.binders_to_string ", " bs1 in
                              let uu____15509 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____15506 uu____15507 uu____15508
                                uu____15509
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv, uu____15552) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t, uu____15558, uu____15559) ->
                     check_function_app t guard
                 | uu____15600 ->
                     let uu____15601 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____15601
                       head1.FStar_Syntax_Syntax.pos in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)
and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
                FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
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
                  let uu____15683 =
                    FStar_List.fold_left2
                      (fun uu____15750 ->
                         fun uu____15751 ->
                           fun uu____15752 ->
                             match (uu____15750, uu____15751, uu____15752)
                             with
                             | ((seen, guard, ghost), (e, aq), (b, aq')) ->
                                 ((let uu____15899 =
                                     let uu____15900 =
                                       FStar_Syntax_Util.eq_aqual aq aq' in
                                     uu____15900 <> FStar_Syntax_Util.Equal in
                                   if uu____15899
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____15902 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____15902 with
                                   | (e1, c1, g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____15930 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____15930 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____15934 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____15934)
                                              &&
                                              (let uu____15936 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____15936)) in
                                       let uu____15937 =
                                         let uu____15948 =
                                           let uu____15959 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____15959] in
                                         FStar_List.append seen uu____15948 in
                                       let uu____15992 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1 in
                                       (uu____15937, uu____15992, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____15683 with
                   | (args1, guard, ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____16054 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____16054
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____16056 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____16056 with | (c2, g) -> (e, c2, g)))
              | uu____16072 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat, FStar_Syntax_Syntax.bv Prims.list,
          FStar_TypeChecker_Env.env, FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.term, FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple6)
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
            let uu____16158 = FStar_Syntax_Util.head_and_args t1 in
            match uu____16158 with
            | (head1, args) ->
                let uu____16201 =
                  let uu____16202 = FStar_Syntax_Subst.compress head1 in
                  uu____16202.FStar_Syntax_Syntax.n in
                (match uu____16201 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____16206;
                        FStar_Syntax_Syntax.vars = uu____16207;_},
                      us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____16214 ->
                     if norm1
                     then t1
                     else
                       (let uu____16216 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1 in
                        aux true uu____16216))
          and unfold_once t f us args =
            let uu____16233 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            if uu____16233
            then t
            else
              (let uu____16235 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               match uu____16235 with
               | FStar_Pervasives_Native.None -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____16255 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
                   (match uu____16255 with
                    | (uu____16260, head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t' in
                        aux false t'1)) in
          let uu____16266 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t in
          aux false uu____16266 in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____16284 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____16284
           then
             let uu____16285 = FStar_Syntax_Print.term_to_string pat_t1 in
             let uu____16286 = FStar_Syntax_Print.term_to_string scrutinee_t in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____16285 uu____16286
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____16300 = FStar_Syntax_Print.term_to_string pat_t1 in
               let uu____16301 =
                 FStar_Syntax_Print.term_to_string scrutinee_t in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____16300 uu____16301 msg in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p in
           let uu____16302 = FStar_Syntax_Util.head_and_args scrutinee_t in
           match uu____16302 with
           | (head_s, args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1 in
               let uu____16346 = FStar_Syntax_Util.un_uinst head_s in
               (match uu____16346 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____16347;
                    FStar_Syntax_Syntax.pos = uu____16348;
                    FStar_Syntax_Syntax.vars = uu____16349;_} ->
                    let uu____16352 = FStar_Syntax_Util.head_and_args pat_t2 in
                    (match uu____16352 with
                     | (head_p, args_p) ->
                         let uu____16395 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s in
                         if uu____16395
                         then
                           let uu____16396 =
                             let uu____16397 =
                               FStar_Syntax_Util.un_uinst head_p in
                             uu____16397.FStar_Syntax_Syntax.n in
                           (match uu____16396 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____16402 =
                                    let uu____16403 =
                                      let uu____16404 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____16404 in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____16403 in
                                  if uu____16402
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____16424 =
                                    let uu____16449 =
                                      let uu____16452 =
                                        FStar_Syntax_Syntax.lid_of_fv f in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____16452 in
                                    match uu____16449 with
                                    | FStar_Pervasives_Native.None ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____16498 =
                                          FStar_Util.first_N n1 args_p in
                                        (match uu____16498 with
                                         | (params_p, uu____16556) ->
                                             let uu____16597 =
                                               FStar_Util.first_N n1 args_s in
                                             (match uu____16597 with
                                              | (params_s, uu____16655) ->
                                                  (params_p, params_s))) in
                                  match uu____16424 with
                                  | (params_p, params_s) ->
                                      FStar_List.fold_left2
                                        (fun out ->
                                           fun uu____16784 ->
                                             fun uu____16785 ->
                                               match (uu____16784,
                                                       uu____16785)
                                               with
                                               | ((p, uu____16819),
                                                  (s, uu____16821)) ->
                                                   let uu____16854 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s in
                                                   (match uu____16854 with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let uu____16857 =
                                                          let uu____16858 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p in
                                                          let uu____16859 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____16858
                                                            uu____16859 in
                                                        fail2 uu____16857
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____16862 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____16864 =
                              let uu____16865 =
                                FStar_Syntax_Print.term_to_string head_p in
                              let uu____16866 =
                                FStar_Syntax_Print.term_to_string head_s in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____16865 uu____16866 in
                            fail2 uu____16864))
                | uu____16867 ->
                    let uu____16868 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t in
                    (match uu____16868 with
                     | FStar_Pervasives_Native.None -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g in
                         g1))) in
        let type_of_simple_pat env1 e =
          let uu____16904 = FStar_Syntax_Util.head_and_args e in
          match uu____16904 with
          | (head1, args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____16968 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____16968 with
                    | (us, t_f) ->
                        let uu____16985 = FStar_Syntax_Util.arrow_formals t_f in
                        (match uu____16985 with
                         | (formals, t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____17111 formals1 args1 =
                                 match uu____17111 with
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
                                          let uu____17256 =
                                            FStar_Syntax_Subst.subst subst1 t in
                                          (pat_e, uu____17256, bvs, guard)
                                      | ((f1, uu____17262)::formals2,
                                         (a, imp_a)::args2) ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort in
                                          let uu____17320 =
                                            let uu____17341 =
                                              let uu____17342 =
                                                FStar_Syntax_Subst.compress a in
                                              uu____17342.FStar_Syntax_Syntax.n in
                                            match uu____17341 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___372_17367 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___372_17367.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___372_17367.FStar_Syntax_Syntax.index);
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
                                                uu____17390 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1 in
                                                let uu____17404 =
                                                  tc_tot_or_gtot_term env2 a in
                                                (match uu____17404 with
                                                 | (a1, uu____17432, g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g in
                                                     let subst2 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst1 in
                                                     ((a1, imp_a), subst2,
                                                       bvs, g1))
                                            | uu____17456 ->
                                                fail1 "Not a simple pattern" in
                                          (match uu____17320 with
                                           | (a1, subst2, bvs1, g) ->
                                               let uu____17517 =
                                                 let uu____17540 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____17540) in
                                               aux uu____17517 formals2 args2)
                                      | uu____17579 ->
                                          fail1 "Not a fully applued pattern") in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____17634 -> fail1 "Not a simple pattern") in
        let rec check_nested_pattern env1 p t =
          (let uu____17682 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns") in
           if uu____17682
           then
             let uu____17683 = FStar_Syntax_Print.pat_to_string p in
             let uu____17684 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____17683
               uu____17684
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____17696 ->
               let uu____17703 =
                 let uu____17704 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____17704 in
               failwith uu____17703
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___373_17717 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___373_17717.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___373_17717.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____17718 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], uu____17718,
                 (let uu___374_17722 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___374_17722.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___375_17725 = x in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___375_17725.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___375_17725.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 } in
               let uu____17726 = FStar_Syntax_Syntax.bv_to_name x1 in
               ([x1], uu____17726,
                 (let uu___376_17730 = p in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___376_17730.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____17731 ->
               let uu____17732 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p in
               (match uu____17732 with
                | (uu____17753, e_c, uu____17755, uu____17756) ->
                    let uu____17761 = tc_tot_or_gtot_term env1 e_c in
                    (match uu____17761 with
                     | (e_c1, lc, g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t in
                           (let uu____17784 =
                              let uu____17785 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t in
                              Prims.op_Negation uu____17785 in
                            if uu____17784
                            then
                              let uu____17786 =
                                let uu____17787 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ in
                                let uu____17788 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____17787 uu____17788 in
                              fail1 uu____17786
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____17838 ->
                        match uu____17838 with
                        | (p1, b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____17863
                                 -> (p1, b)
                             | uu____17872 ->
                                 let uu____17873 =
                                   let uu____17876 =
                                     let uu____17877 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun in
                                     FStar_Syntax_Syntax.Pat_var uu____17877 in
                                   FStar_Syntax_Syntax.withinfo uu____17876
                                     p1.FStar_Syntax_Syntax.p in
                                 (uu____17873, b))) sub_pats in
                 let uu___377_17880 = p in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___377_17880.FStar_Syntax_Syntax.p)
                 } in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____17920 ->
                         match uu____17920 with
                         | (x, uu____17928) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____17933
                                  -> false
                              | uu____17940 -> true))) in
               let uu____17941 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat in
               (match uu____17941 with
                | (simple_bvs, simple_pat_e, g0, simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____17975 =
                          let uu____17976 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p in
                          let uu____17977 =
                            FStar_Syntax_Print.pat_to_string simple_pat in
                          let uu____17978 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1) in
                          let uu____17983 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs) in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____17976 uu____17977 uu____17978 uu____17983 in
                        failwith uu____17975)
                     else ();
                     (let uu____17985 =
                        let uu____17994 =
                          type_of_simple_pat env1 simple_pat_e in
                        match uu____17994 with
                        | (simple_pat_e1, simple_pat_t, simple_bvs1, guard)
                            ->
                            let g' =
                              let uu____18022 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t in
                              pat_typ_ok env1 simple_pat_t uu____18022 in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g' in
                            ((let uu____18025 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns") in
                              if uu____18025
                              then
                                let uu____18026 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1 in
                                let uu____18027 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t in
                                let uu____18028 =
                                  let uu____18029 =
                                    FStar_List.map
                                      (fun x ->
                                         let uu____18035 =
                                           let uu____18036 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           let uu____18037 =
                                             let uu____18038 =
                                               let uu____18039 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort in
                                               Prims.strcat uu____18039 ")" in
                                             Prims.strcat " : " uu____18038 in
                                           Prims.strcat uu____18036
                                             uu____18037 in
                                         Prims.strcat "(" uu____18035)
                                      simple_bvs1 in
                                  FStar_All.pipe_right uu____18029
                                    (FStar_String.concat " ") in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____18026 uu____18027 uu____18028
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1)) in
                      match uu____17985 with
                      | (simple_pat_e1, simple_bvs1, g1) ->
                          let uu____18062 =
                            let uu____18083 =
                              let uu____18104 =
                                FStar_TypeChecker_Env.conj_guard g0 g1 in
                              (env1, [], [], [], uu____18104) in
                            FStar_List.fold_left2
                              (fun uu____18161 ->
                                 fun uu____18162 ->
                                   fun x ->
                                     match (uu____18161, uu____18162) with
                                     | ((env2, bvs, pats, subst1, g),
                                        (p1, b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort in
                                         let uu____18284 =
                                           check_nested_pattern env2 p1
                                             expected_t in
                                         (match uu____18284 with
                                          | (bvs_p, e_p, p2, g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p in
                                              let uu____18324 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g' in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____18324))) uu____18083
                              sub_pats1 simple_bvs1 in
                          (match uu____18062 with
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
                                              let uu___378_18516 = hd1 in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___378_18516.FStar_Syntax_Syntax.p)
                                              } in
                                            let uu____18521 =
                                              aux simple_pats1 bvs1 sub_pats2 in
                                            (hd2, b) :: uu____18521
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,
                                                (hd2, uu____18560)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____18592 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3 in
                                                 (hd2, b) :: uu____18592
                                             | uu____18609 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____18632 ->
                                            failwith
                                              "Impossible: expected a simple pattern") in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1, simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats in
                                     let uu___379_18670 = pat in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___379_18670.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____18681 -> failwith "Impossible" in
                               let uu____18684 =
                                 reconstruct_nested_pat simple_pat_elab in
                               (bvs, pat_e, uu____18684, g)))))) in
        (let uu____18688 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns") in
         if uu____18688
         then
           let uu____18689 = FStar_Syntax_Print.pat_to_string p0 in
           FStar_Util.print1 "Checking pattern: %s\n" uu____18689
         else ());
        (let uu____18691 =
           let uu____18702 =
             let uu___380_18703 =
               let uu____18704 = FStar_TypeChecker_Env.clear_expected_typ env in
               FStar_All.pipe_right uu____18704 FStar_Pervasives_Native.fst in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___380_18703.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___380_18703.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___380_18703.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___380_18703.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___380_18703.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___380_18703.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___380_18703.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___380_18703.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___380_18703.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___380_18703.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___380_18703.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___380_18703.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___380_18703.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___380_18703.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___380_18703.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___380_18703.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___380_18703.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___380_18703.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___380_18703.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___380_18703.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___380_18703.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___380_18703.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___380_18703.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___380_18703.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___380_18703.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___380_18703.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___380_18703.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___380_18703.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___380_18703.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___380_18703.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___380_18703.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___380_18703.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___380_18703.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___380_18703.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___380_18703.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___380_18703.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___380_18703.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___380_18703.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___380_18703.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___380_18703.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___380_18703.FStar_TypeChecker_Env.nbe)
             } in
           let uu____18719 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0 in
           check_nested_pattern uu____18702 uu____18719 pat_t in
         match uu____18691 with
         | (bvs, pat_e, pat, g) ->
             ((let uu____18743 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns") in
               if uu____18743
               then
                 let uu____18744 = FStar_Syntax_Print.pat_to_string pat in
                 let uu____18745 = FStar_Syntax_Print.term_to_string pat_e in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____18744
                   uu____18745
               else ());
              (let uu____18747 = FStar_TypeChecker_Env.push_bvs env bvs in
               let uu____18748 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e in
               (pat, bvs, uu____18747, pat_e, uu____18748, g))))
and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
          FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,
           FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
           FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3,
          FStar_Syntax_Syntax.term, FStar_Ident.lident,
          FStar_Syntax_Syntax.cflags Prims.list,
          Prims.bool -> FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple6)
  =
  fun scrutinee ->
    fun env ->
      fun branch1 ->
        let uu____18793 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____18793 with
        | (pattern, when_clause, branch_exp) ->
            let uu____18838 = branch1 in
            (match uu____18838 with
             | (cpat, uu____18879, cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____18901 =
                   let uu____18908 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____18908
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____18901 with
                  | (scrutinee_env, uu____18941) ->
                      let uu____18946 = tc_pat env pat_t pattern in
                      (match uu____18946 with
                       | (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp,
                          guard_pat) ->
                           let uu____18996 =
                             match when_clause with
                             | FStar_Pervasives_Native.None ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____19026 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____19026
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____19044 =
                                      let uu____19051 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____19051 e in
                                    match uu____19044 with
                                    | (e1, c, g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____18996 with
                            | (when_clause1, g_when) ->
                                let uu____19104 = tc_term pat_env branch_exp in
                                (match uu____19104 with
                                 | (branch_exp1, c, g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____19158 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool in
                                             FStar_All.pipe_left
                                               (fun _0_17 ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_17) uu____19158 in
                                       let uu____19169 =
                                         let eqs =
                                           let uu____19190 =
                                             let uu____19191 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env in
                                             Prims.op_Negation uu____19191 in
                                           if uu____19190
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____19204 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____19219 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____19222 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____19225 ->
                                                  let uu____19226 =
                                                    let uu____19229 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____19229 pat_t
                                                      scrutinee_tm e in
                                                  FStar_Pervasives_Native.Some
                                                    uu____19226) in
                                         let uu____19232 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch in
                                         match uu____19232 with
                                         | (c1, g_branch1) ->
                                             let uu____19257 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____19274 when
                                                   let uu____19287 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____19287
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
                                                   let uu____19317 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf in
                                                   let uu____19318 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when in
                                                   (uu____19317, uu____19318)
                                               | (FStar_Pervasives_Native.Some
                                                  f,
                                                  FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f in
                                                   let g_fw =
                                                     let uu____19339 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____19339 in
                                                   let uu____19340 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw in
                                                   let uu____19341 =
                                                     let uu____19342 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____19342 g_when in
                                                   (uu____19340, uu____19341)
                                               | (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_w =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       w in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       g_w in
                                                   let uu____19360 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w in
                                                   (uu____19360, g_when) in
                                             (match uu____19257 with
                                              | (c_weak, g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1 in
                                                  let maybe_return_c_weak
                                                    should_return =
                                                    let c_weak1 =
                                                      let uu____19400 =
                                                        should_return &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak) in
                                                      if uu____19400
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1 in
                                                  let uu____19402 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak in
                                                  let uu____19403 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1 in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____19402, uu____19403)) in
                                       match uu____19169 with
                                       | (effect_label, cflags,
                                          maybe_return_c, g_when1, g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____19450 =
                                               let uu____19451 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env in
                                               Prims.op_Negation uu____19451 in
                                             if uu____19450
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____19493 =
                                                      let uu____19494 =
                                                        let uu____19495 =
                                                          let uu____19498 =
                                                            let uu____19505 =
                                                              FStar_TypeChecker_Env.typ_of_datacon
                                                                env
                                                                f.FStar_Syntax_Syntax.v in
                                                            FStar_TypeChecker_Env.datacons_of_typ
                                                              env uu____19505 in
                                                          FStar_Pervasives_Native.snd
                                                            uu____19498 in
                                                        FStar_List.length
                                                          uu____19495 in
                                                      uu____19494 >
                                                        (Prims.parse_int "1") in
                                                    if uu____19493
                                                    then
                                                      let discriminator =
                                                        FStar_Syntax_Util.mk_discriminator
                                                          f.FStar_Syntax_Syntax.v in
                                                      let uu____19511 =
                                                        FStar_TypeChecker_Env.try_lookup_lid
                                                          env discriminator in
                                                      match uu____19511 with
                                                      | FStar_Pervasives_Native.None
                                                          -> []
                                                      | uu____19532 ->
                                                          let disc =
                                                            FStar_Syntax_Syntax.fvar
                                                              discriminator
                                                              (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                 (Prims.parse_int "1"))
                                                              FStar_Pervasives_Native.None in
                                                          let disc1 =
                                                            let uu____19547 =
                                                              let uu____19552
                                                                =
                                                                let uu____19553
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2 in
                                                                [uu____19553] in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____19552 in
                                                            uu____19547
                                                              FStar_Pervasives_Native.None
                                                              scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                          let uu____19580 =
                                                            FStar_Syntax_Util.mk_eq2
                                                              FStar_Syntax_Syntax.U_zero
                                                              FStar_Syntax_Util.t_bool
                                                              disc1
                                                              FStar_Syntax_Util.exp_true_bool in
                                                          [uu____19580]
                                                    else [] in
                                                  let fail1 uu____19587 =
                                                    let uu____19588 =
                                                      let uu____19589 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos in
                                                      let uu____19590 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1 in
                                                      let uu____19591 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1 in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____19589
                                                        uu____19590
                                                        uu____19591 in
                                                    failwith uu____19588 in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1, uu____19604) ->
                                                        head_constructor t1
                                                    | uu____19609 -> fail1 () in
                                                  let pat_exp2 =
                                                    let uu____19613 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1 in
                                                    FStar_All.pipe_right
                                                      uu____19613
                                                      FStar_Syntax_Util.unmeta in
                                                  match pat_exp2.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      uu____19618 -> []
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_uvar
                                                           uu____19631;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu____19632;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu____19633;_},
                                                       uu____19634)
                                                      -> []
                                                  | FStar_Syntax_Syntax.Tm_name
                                                      uu____19671 -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      (FStar_Const.Const_unit)
                                                      -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      c1 ->
                                                      let uu____19673 =
                                                        let uu____19674 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1 in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____19674
                                                          scrutinee_tm1
                                                          pat_exp2 in
                                                      [uu____19673]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      uu____19675 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2 in
                                                      let uu____19683 =
                                                        let uu____19684 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v in
                                                        Prims.op_Negation
                                                          uu____19684 in
                                                      if uu____19683
                                                      then []
                                                      else
                                                        (let uu____19688 =
                                                           head_constructor
                                                             pat_exp2 in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____19688)
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      uu____19691 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2 in
                                                      let uu____19693 =
                                                        let uu____19694 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v in
                                                        Prims.op_Negation
                                                          uu____19694 in
                                                      if uu____19693
                                                      then []
                                                      else
                                                        (let uu____19698 =
                                                           head_constructor
                                                             pat_exp2 in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____19698)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1, args) ->
                                                      let f =
                                                        head_constructor
                                                          head1 in
                                                      let uu____19728 =
                                                        let uu____19729 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v in
                                                        Prims.op_Negation
                                                          uu____19729 in
                                                      if uu____19728
                                                      then []
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____19736 =
                                                             FStar_All.pipe_right
                                                               args
                                                               (FStar_List.mapi
                                                                  (fun i ->
                                                                    fun
                                                                    uu____19772
                                                                    ->
                                                                    match uu____19772
                                                                    with
                                                                    | 
                                                                    (ei,
                                                                    uu____19784)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____19794
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____19794
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> []
                                                                    | 
                                                                    uu____19815
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____19829
                                                                    =
                                                                    let uu____19834
                                                                    =
                                                                    let uu____19835
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____19835
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____19836
                                                                    =
                                                                    let uu____19837
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____19837] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____19834
                                                                    uu____19836 in
                                                                    uu____19829
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                           FStar_All.pipe_right
                                                             uu____19736
                                                             FStar_List.flatten in
                                                         let uu____19870 =
                                                           discriminate
                                                             scrutinee_tm1 f in
                                                         FStar_List.append
                                                           uu____19870
                                                           sub_term_guards)
                                                  | uu____19873 -> [] in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pat =
                                                  let uu____19889 =
                                                    let uu____19890 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env in
                                                    Prims.op_Negation
                                                      uu____19890 in
                                                  if uu____19889
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____19893 =
                                                         build_branch_guard
                                                           scrutinee_tm1 pat in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____19893 in
                                                     let uu____19902 =
                                                       FStar_Syntax_Util.type_u
                                                         () in
                                                     match uu____19902 with
                                                     | (k, uu____19908) ->
                                                         let uu____19909 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k in
                                                         (match uu____19909
                                                          with
                                                          | (t1, uu____19917,
                                                             uu____19918) ->
                                                              t1)) in
                                                let branch_guard =
                                                  build_and_check_branch_guard
                                                    scrutinee_tm norm_pat_exp in
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
                                           ((let uu____19930 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High in
                                             if uu____19930
                                             then
                                               let uu____19931 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____19931
                                             else ());
                                            (let uu____19933 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1) in
                                             let uu____19950 =
                                               let uu____19951 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1 in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____19951 guard in
                                             (uu____19933, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____19950))))))))))
and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let uu____19994 = check_let_bound_def true env1 lb in
          (match uu____19994 with
           | (e1, univ_vars1, c1, g1, annotated) ->
               let uu____20016 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____20037 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____20037, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____20042 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____20042
                        (FStar_TypeChecker_Rel.resolve_implicits env1) in
                    let uu____20044 =
                      let uu____20057 =
                        let uu____20072 =
                          let uu____20081 =
                            let uu____20088 =
                              FStar_Syntax_Syntax.lcomp_comp c1 in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____20088) in
                          [uu____20081] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____20072 in
                      FStar_List.hd uu____20057 in
                    match uu____20044 with
                    | (uu____20123, univs1, e11, c11, gvs) ->
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
                        let uu____20137 = FStar_Syntax_Util.lcomp_of_comp c11 in
                        (g13, e11, univs1, uu____20137)) in
               (match uu____20016 with
                | (g11, e11, univ_vars2, c11) ->
                    let uu____20154 =
                      let uu____20163 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____20163
                      then
                        let uu____20172 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____20172 with
                        | (ok, c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____20201 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____20201
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____20202 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____20202, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____20216 =
                              FStar_Syntax_Syntax.lcomp_comp c11 in
                            FStar_All.pipe_right uu____20216
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1) in
                          let e21 =
                            let uu____20222 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____20222
                            then e2
                            else
                              ((let uu____20227 =
                                  FStar_TypeChecker_Env.get_range env1 in
                                FStar_Errors.log_issue uu____20227
                                  FStar_TypeChecker_Err.top_level_effect);
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect)))
                                 FStar_Pervasives_Native.None
                                 e2.FStar_Syntax_Syntax.pos) in
                          (e21, c))) in
                    (match uu____20154 with
                     | (e21, c12) ->
                         ((let uu____20251 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium in
                           if uu____20251
                           then
                             let uu____20252 =
                               FStar_Syntax_Print.term_to_string e11 in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____20252
                           else ());
                          (let e12 =
                             let uu____20255 = FStar_Options.tcnorm () in
                             if uu____20255
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
                           (let uu____20258 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium in
                            if uu____20258
                            then
                              let uu____20259 =
                                FStar_Syntax_Print.term_to_string e12 in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____20259
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
                            let uu____20265 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos in
                            let uu____20276 =
                              FStar_Syntax_Util.lcomp_of_comp cres in
                            (uu____20265, uu____20276,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____20277 -> failwith "Impossible"
and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
          let env2 =
            let uu___381_20308 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___381_20308.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___381_20308.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___381_20308.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___381_20308.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___381_20308.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___381_20308.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___381_20308.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___381_20308.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___381_20308.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___381_20308.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___381_20308.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___381_20308.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___381_20308.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___381_20308.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___381_20308.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___381_20308.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___381_20308.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___381_20308.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___381_20308.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___381_20308.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___381_20308.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___381_20308.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___381_20308.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___381_20308.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___381_20308.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___381_20308.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___381_20308.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___381_20308.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___381_20308.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___381_20308.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___381_20308.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___381_20308.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___381_20308.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___381_20308.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___381_20308.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___381_20308.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___381_20308.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___381_20308.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___381_20308.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___381_20308.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___381_20308.FStar_TypeChecker_Env.nbe)
            } in
          let uu____20309 =
            let uu____20320 =
              let uu____20321 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____20321 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____20320 lb in
          (match uu____20309 with
           | (e1, uu____20343, c1, g1, annotated) ->
               ((let uu____20348 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____20352 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1 in
                      Prims.op_Negation uu____20352) in
                 if uu____20348
                 then
                   let uu____20353 =
                     let uu____20358 =
                       let uu____20359 = FStar_Syntax_Print.term_to_string e1 in
                       let uu____20360 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____20359 uu____20360 in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____20358) in
                   FStar_Errors.raise_error uu____20353
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___382_20363 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___382_20363.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___382_20363.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   } in
                 let uu____20364 =
                   let uu____20369 =
                     let uu____20370 = FStar_Syntax_Syntax.mk_binder x in
                     [uu____20370] in
                   FStar_Syntax_Subst.open_term uu____20369 e2 in
                 match uu____20364 with
                 | (xb, e21) ->
                     let xbinder = FStar_List.hd xb in
                     let x1 = FStar_Pervasives_Native.fst xbinder in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                     let uu____20414 = tc_term env_x e21 in
                     (match uu____20414 with
                      | (e22, c2, g2) ->
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c2) in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c2.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_Syntax_Syntax.res_typ
                              cres.FStar_Syntax_Syntax.eff_name e11
                              lb.FStar_Syntax_Syntax.lbattrs
                              lb.FStar_Syntax_Syntax.lbpos in
                          let e3 =
                            let uu____20439 =
                              let uu____20446 =
                                let uu____20447 =
                                  let uu____20460 =
                                    FStar_Syntax_Subst.close xb e23 in
                                  ((false, [lb1]), uu____20460) in
                                FStar_Syntax_Syntax.Tm_let uu____20447 in
                              FStar_Syntax_Syntax.mk uu____20446 in
                            uu____20439 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ in
                          let x_eq_e1 =
                            let uu____20478 =
                              let uu____20479 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ in
                              let uu____20480 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              FStar_Syntax_Util.mk_eq2 uu____20479
                                c1.FStar_Syntax_Syntax.res_typ uu____20480
                                e11 in
                            FStar_All.pipe_left
                              (fun _0_18 ->
                                 FStar_TypeChecker_Common.NonTrivial _0_18)
                              uu____20478 in
                          let g21 =
                            let uu____20482 =
                              let uu____20483 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1 in
                              FStar_TypeChecker_Env.imp_guard uu____20483 g2 in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____20482 in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21 in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22 in
                          let uu____20486 =
                            let uu____20487 =
                              FStar_TypeChecker_Env.expected_typ env2 in
                            FStar_Option.isSome uu____20487 in
                          if uu____20486
                          then
                            let tt =
                              let uu____20497 =
                                FStar_TypeChecker_Env.expected_typ env2 in
                              FStar_All.pipe_right uu____20497
                                FStar_Option.get in
                            ((let uu____20503 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports") in
                              if uu____20503
                              then
                                let uu____20504 =
                                  FStar_Syntax_Print.term_to_string tt in
                                let uu____20505 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____20504 uu____20505
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____20508 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                             match uu____20508 with
                             | (t, g_ex) ->
                                 ((let uu____20522 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports") in
                                   if uu____20522
                                   then
                                     let uu____20523 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ in
                                     let uu____20524 =
                                       FStar_Syntax_Print.term_to_string t in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____20523 uu____20524
                                   else ());
                                  (let uu____20526 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard in
                                   (e4,
                                     (let uu___383_20528 = cres in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___383_20528.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___383_20528.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___383_20528.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____20526))))))))
      | uu____20529 ->
          failwith "Impossible (inner let with more than one lb)"
and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____20561 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____20561 with
           | (lbs1, e21) ->
               let uu____20580 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____20580 with
                | (env0, topt) ->
                    let uu____20599 = build_let_rec_env true env0 lbs1 in
                    (match uu____20599 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____20621 = check_let_recs rec_env lbs2 in
                         (match uu____20621 with
                          | (lbs3, g_lbs) ->
                              let g_lbs1 =
                                let uu____20641 =
                                  let uu____20642 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs in
                                  FStar_All.pipe_right uu____20642
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1) in
                                FStar_All.pipe_right uu____20641
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1) in
                              let all_lb_names =
                                let uu____20648 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____20648
                                  (fun _0_19 ->
                                     FStar_Pervasives_Native.Some _0_19) in
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
                                     let uu____20697 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb ->
                                               let uu____20731 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____20731))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____20697 in
                                   FStar_List.map2
                                     (fun uu____20765 ->
                                        fun lb ->
                                          match uu____20765 with
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
                                let uu____20813 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____20813 in
                              let uu____20814 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____20814 with
                               | (lbs5, e22) ->
                                   ((let uu____20834 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____20834
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____20835 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____20835, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____20846 -> failwith "Impossible"
and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun top ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) ->
          let uu____20878 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____20878 with
           | (lbs1, e21) ->
               let uu____20897 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____20897 with
                | (env0, topt) ->
                    let uu____20916 = build_let_rec_env false env0 lbs1 in
                    (match uu____20916 with
                     | (lbs2, rec_env, g_t) ->
                         let uu____20938 =
                           let uu____20945 = check_let_recs rec_env lbs2 in
                           FStar_All.pipe_right uu____20945
                             (fun uu____20968 ->
                                match uu____20968 with
                                | (lbs3, g) ->
                                    let uu____20987 =
                                      FStar_TypeChecker_Env.conj_guard g_t g in
                                    (lbs3, uu____20987)) in
                         (match uu____20938 with
                          | (lbs3, g_lbs) ->
                              let uu____21002 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2 ->
                                        fun lb ->
                                          let x =
                                            let uu___384_21025 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___384_21025.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___384_21025.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___385_21027 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___385_21027.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____21002 with
                               | (env2, lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____21054 = tc_term env2 e21 in
                                   (match uu____21054 with
                                    | (e22, cres, g2) ->
                                        let cres1 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres in
                                        let cres2 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres1
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____21073 =
                                            let uu____21074 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____21074 g2 in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____21073 in
                                        let cres3 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres2 in
                                        let tres =
                                          norm env2
                                            cres3.FStar_Syntax_Syntax.res_typ in
                                        let cres4 =
                                          let uu___386_21084 = cres3 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___386_21084.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___386_21084.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___386_21084.FStar_Syntax_Syntax.comp_thunk)
                                          } in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb ->
                                                    let uu____21092 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____21092)) in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard in
                                        let uu____21093 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____21093 with
                                         | (lbs5, e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____21131 ->
                                                  (e, cres4, guard1)
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  let uu____21132 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  (match uu____21132 with
                                                   | (tres1, g_ex) ->
                                                       let cres5 =
                                                         let uu___387_21146 =
                                                           cres4 in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___387_21146.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___387_21146.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___387_21146.FStar_Syntax_Syntax.comp_thunk)
                                                         } in
                                                       let uu____21147 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1 in
                                                       (e, cres5,
                                                         uu____21147))))))))))
      | uu____21148 -> failwith "Impossible"
and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,
          FStar_TypeChecker_Env.env_t, FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun top_level ->
    fun env ->
      fun lbs ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____21193 = FStar_Options.ml_ish () in
          if uu____21193
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____21196 = FStar_Syntax_Util.arrow_formals_comp t in
             match uu____21196 with
             | (formals, c) ->
                 let uu____21227 = FStar_Syntax_Util.abs_formals lbdef in
                 (match uu____21227 with
                  | (actuals, uu____21237, uu____21238) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____21255 =
                          let uu____21260 =
                            let uu____21261 =
                              FStar_Syntax_Print.term_to_string lbdef in
                            let uu____21262 =
                              FStar_Syntax_Print.term_to_string lbtyp in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____21261 uu____21262 in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____21260) in
                        FStar_Errors.raise_error uu____21255
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____21265 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____21265 actuals in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1 in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____21292 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____21292) in
                            let formals_msg =
                              let n1 = FStar_List.length formals in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____21312 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments"
                                   uu____21312) in
                            let msg =
                              let uu____21320 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              let uu____21321 =
                                FStar_Syntax_Print.lbname_to_string lbname in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____21320 uu____21321 formals_msg
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
        let uu____21328 =
          FStar_List.fold_left
            (fun uu____21361 ->
               fun lb ->
                 match uu____21361 with
                 | (lbs1, env1, g_acc) ->
                     let uu____21386 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____21386 with
                      | (univ_vars1, t, check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1 in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let uu____21406 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1 in
                               let uu____21423 =
                                 let uu____21430 =
                                   let uu____21431 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____21431 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___388_21442 = env01 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___388_21442.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___388_21442.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___388_21442.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___388_21442.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___388_21442.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___388_21442.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___388_21442.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___388_21442.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___388_21442.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___388_21442.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___388_21442.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___388_21442.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___388_21442.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___388_21442.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___388_21442.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___388_21442.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___388_21442.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___388_21442.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___388_21442.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___388_21442.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___388_21442.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___388_21442.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___388_21442.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___388_21442.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___388_21442.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___388_21442.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___388_21442.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___388_21442.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___388_21442.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___388_21442.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___388_21442.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___388_21442.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___388_21442.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___388_21442.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___388_21442.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___388_21442.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___388_21442.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___388_21442.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___388_21442.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___388_21442.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___388_21442.FStar_TypeChecker_Env.nbe)
                                    }) t uu____21430 in
                               match uu____21423 with
                               | (t1, uu____21450, g) ->
                                   let uu____21452 =
                                     let uu____21453 =
                                       let uu____21454 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2) in
                                       FStar_All.pipe_right uu____21454
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2) in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____21453 in
                                   let uu____21455 = norm env01 t1 in
                                   (uu____21452, uu____21455)) in
                          (match uu____21406 with
                           | (g, t1) ->
                               let env3 =
                                 let uu____21475 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1 in
                                 if uu____21475
                                 then
                                   let uu___389_21476 = env2 in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___389_21476.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___389_21476.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___389_21476.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___389_21476.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___389_21476.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___389_21476.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___389_21476.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___389_21476.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___389_21476.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___389_21476.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___389_21476.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___389_21476.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___389_21476.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___389_21476.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___389_21476.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___389_21476.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___389_21476.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___389_21476.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___389_21476.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___389_21476.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___389_21476.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___389_21476.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___389_21476.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___389_21476.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___389_21476.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___389_21476.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___389_21476.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___389_21476.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___389_21476.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___389_21476.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___389_21476.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___389_21476.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___389_21476.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___389_21476.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___389_21476.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___389_21476.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___389_21476.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___389_21476.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___389_21476.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___389_21476.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___389_21476.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1) in
                               let lb1 =
                                 let uu___390_21489 = lb in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___390_21489.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___390_21489.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___390_21489.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___390_21489.FStar_Syntax_Syntax.lbpos)
                                 } in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs in
        match uu____21328 with
        | (lbs1, env1, g) -> ((FStar_List.rev lbs1), env1, g)
and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lbs ->
      let uu____21515 =
        let uu____21524 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb ->
                  let uu____21550 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____21550 with
                  | (bs, t, lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____21580 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____21580
                       | uu____21585 ->
                           let lb1 =
                             let uu___391_21588 = lb in
                             let uu____21589 =
                               FStar_Syntax_Util.abs bs t lcomp in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____21589;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___391_21588.FStar_Syntax_Syntax.lbpos)
                             } in
                           let uu____21592 =
                             let uu____21599 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp in
                             tc_tot_or_gtot_term uu____21599
                               lb1.FStar_Syntax_Syntax.lbdef in
                           (match uu____21592 with
                            | (e, c, g) ->
                                ((let uu____21608 =
                                    let uu____21609 =
                                      FStar_Syntax_Util.is_total_lcomp c in
                                    Prims.op_Negation uu____21609 in
                                  if uu____21608
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
        FStar_All.pipe_right uu____21524 FStar_List.unzip in
      match uu____21515 with
      | (lbs1, gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard in
          (lbs1, g_lbs)
and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.univ_names,
          FStar_Syntax_Syntax.lcomp, FStar_TypeChecker_Env.guard_t,
          Prims.bool) FStar_Pervasives_Native.tuple5)
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let uu____21658 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____21658 with
        | (env1, uu____21676) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____21684 = check_lbtyp top_level env lb in
            (match uu____21684 with
             | (topt, wf_annot, univ_vars1, univ_opening, env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____21728 =
                     tc_maybe_toplevel_term
                       (let uu___392_21737 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___392_21737.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___392_21737.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___392_21737.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___392_21737.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___392_21737.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___392_21737.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___392_21737.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___392_21737.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___392_21737.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___392_21737.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___392_21737.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___392_21737.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___392_21737.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___392_21737.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___392_21737.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___392_21737.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___392_21737.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___392_21737.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___392_21737.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___392_21737.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___392_21737.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___392_21737.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___392_21737.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___392_21737.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___392_21737.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___392_21737.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___392_21737.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___392_21737.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___392_21737.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___392_21737.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___392_21737.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___392_21737.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___392_21737.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___392_21737.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___392_21737.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___392_21737.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___392_21737.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___392_21737.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___392_21737.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___392_21737.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___392_21737.FStar_TypeChecker_Env.nbe)
                        }) e11 in
                   match uu____21728 with
                   | (e12, c1, g1) ->
                       let uu____21751 =
                         let uu____21756 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____21761 ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____21756 e12 c1 wf_annot in
                       (match uu____21751 with
                        | (c11, guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f in
                            ((let uu____21776 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____21776
                              then
                                let uu____21777 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____21778 =
                                  FStar_Syntax_Print.lcomp_to_string c11 in
                                let uu____21779 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____21777 uu____21778 uu____21779
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
          FStar_TypeChecker_Env.guard_t, FStar_Syntax_Syntax.univ_names,
          FStar_Syntax_Syntax.subst_elt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple5)
  =
  fun top_level ->
    fun env ->
      fun lb ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____21813 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____21813 with
             | (univ_opening, univ_vars1) ->
                 let uu____21846 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____21846))
        | uu____21851 ->
            let uu____21852 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____21852 with
             | (univ_opening, univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____21901 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____21901)
                 else
                   (let uu____21907 = FStar_Syntax_Util.type_u () in
                    match uu____21907 with
                    | (k, uu____21927) ->
                        let uu____21928 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____21928 with
                         | (t2, uu____21950, g) ->
                             ((let uu____21953 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____21953
                               then
                                 let uu____21954 =
                                   let uu____21955 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____21955 in
                                 let uu____21956 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____21954 uu____21956
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____21959 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____21959))))))
and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,
         FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2,
        FStar_TypeChecker_Env.env, FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env ->
    fun uu____21965 ->
      match uu____21965 with
      | (x, imp) ->
          let uu____21992 = FStar_Syntax_Util.type_u () in
          (match uu____21992 with
           | (tu, u) ->
               ((let uu____22014 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____22014
                 then
                   let uu____22015 = FStar_Syntax_Print.bv_to_string x in
                   let uu____22016 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____22017 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____22015 uu____22016 uu____22017
                 else ());
                (let uu____22019 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____22019 with
                 | (t, uu____22041, g) ->
                     let uu____22043 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____22059 = tc_tactic env tau in
                           (match uu____22059 with
                            | (tau1, uu____22073, g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____22077 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard) in
                     (match uu____22043 with
                      | (imp1, g') ->
                          let x1 =
                            ((let uu___393_22112 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___393_22112.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___393_22112.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1) in
                          ((let uu____22114 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____22114
                            then
                              let uu____22115 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1) in
                              let uu____22118 =
                                FStar_Syntax_Print.term_to_string t in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____22115
                                uu____22118
                            else ());
                           (let uu____22120 = push_binding env x1 in
                            (x1, uu____22120, g, u)))))))
and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders, FStar_TypeChecker_Env.env,
        FStar_TypeChecker_Env.guard_t, FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple4)
  =
  fun env ->
    fun bs ->
      (let uu____22132 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
       if uu____22132
       then
         let uu____22133 = FStar_Syntax_Print.binders_to_string ", " bs in
         FStar_Util.print1 "Checking binders %s\n" uu____22133
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____22242 = tc_binder env1 b in
             (match uu____22242 with
              | (b1, env', g, u) ->
                  let uu____22291 = aux env' bs2 in
                  (match uu____22291 with
                   | (bs3, env'1, g', us) ->
                       let uu____22352 =
                         let uu____22353 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g' in
                         FStar_TypeChecker_Env.conj_guard g uu____22353 in
                       ((b1 :: bs3), env'1, uu____22352, (u :: us)))) in
       aux env bs)
and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
         FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun pats ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____22460 ->
             fun uu____22461 ->
               match (uu____22460, uu____22461) with
               | ((t, imp), (args1, g)) ->
                   let uu____22552 = tc_term env1 t in
                   (match uu____22552 with
                    | (t1, uu____22572, g') ->
                        let uu____22574 =
                          FStar_TypeChecker_Env.conj_guard g g' in
                        (((t1, imp) :: args1), uu____22574))) args
          ([], FStar_TypeChecker_Env.trivial_guard) in
      FStar_List.fold_right
        (fun p ->
           fun uu____22628 ->
             match uu____22628 with
             | (pats1, g) ->
                 let uu____22655 = tc_args env p in
                 (match uu____22655 with
                  | (args, g') ->
                      let uu____22668 = FStar_TypeChecker_Env.conj_guard g g' in
                      ((args :: pats1), uu____22668))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)
and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let uu____22681 = tc_maybe_toplevel_term env e in
      match uu____22681 with
      | (e1, c, g) ->
          let uu____22697 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____22697
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c in
             let c2 = norm_c env c1 in
             let uu____22708 =
               let uu____22713 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____22713
               then
                 let uu____22718 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____22718, false)
               else
                 (let uu____22720 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____22720, true)) in
             match uu____22708 with
             | (target_comp, allow_ghost) ->
                 let uu____22729 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____22729 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____22739 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp in
                      let uu____22740 =
                        FStar_TypeChecker_Env.conj_guard g1 g' in
                      (e1, uu____22739, uu____22740)
                  | uu____22741 ->
                      if allow_ghost
                      then
                        let uu____22750 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2 in
                        FStar_Errors.raise_error uu____22750
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____22762 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2 in
                         FStar_Errors.raise_error uu____22762
                           e1.FStar_Syntax_Syntax.pos)))
and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      fun t ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t ->
      let uu____22785 = tc_tot_or_gtot_term env t in
      match uu____22785 with
      | (t1, c, g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      (let uu____22817 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22817
       then
         let uu____22818 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____22818
       else ());
      (let env1 =
         let uu___394_22821 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___394_22821.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___394_22821.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___394_22821.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___394_22821.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___394_22821.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___394_22821.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___394_22821.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___394_22821.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___394_22821.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___394_22821.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___394_22821.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___394_22821.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___394_22821.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___394_22821.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___394_22821.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___394_22821.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___394_22821.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___394_22821.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___394_22821.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___394_22821.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___394_22821.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___394_22821.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___394_22821.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___394_22821.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___394_22821.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___394_22821.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___394_22821.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___394_22821.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___394_22821.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___394_22821.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___394_22821.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___394_22821.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___394_22821.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___394_22821.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___394_22821.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___394_22821.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___394_22821.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___394_22821.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___394_22821.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___394_22821.FStar_TypeChecker_Env.nbe)
         } in
       let uu____22828 =
         try
           (fun uu___396_22842 ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1, msg, uu____22863) ->
             let uu____22864 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____22864 in
       match uu____22828 with
       | (t, c, g) ->
           let uu____22880 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____22880
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____22888 =
                let uu____22893 =
                  let uu____22894 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____22894 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____22893) in
              let uu____22895 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____22888 uu____22895))
let level_of_type_fail :
  'Auu____22910 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____22910
  =
  fun env ->
    fun e ->
      fun t ->
        let uu____22926 =
          let uu____22931 =
            let uu____22932 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____22932 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____22931) in
        let uu____22933 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____22926 uu____22933
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      fun t ->
        let rec aux retry t1 =
          let uu____22968 =
            let uu____22969 = FStar_Syntax_Util.unrefine t1 in
            uu____22969.FStar_Syntax_Syntax.n in
          match uu____22968 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____22973 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1 in
                aux false t2
              else
                (let uu____22976 = FStar_Syntax_Util.type_u () in
                 match uu____22976 with
                 | (t_u, u) ->
                     let env1 =
                       let uu___397_22984 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___397_22984.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___397_22984.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___397_22984.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___397_22984.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___397_22984.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___397_22984.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___397_22984.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___397_22984.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___397_22984.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___397_22984.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___397_22984.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___397_22984.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___397_22984.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___397_22984.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___397_22984.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___397_22984.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___397_22984.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___397_22984.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___397_22984.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___397_22984.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___397_22984.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___397_22984.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___397_22984.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___397_22984.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___397_22984.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___397_22984.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___397_22984.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___397_22984.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___397_22984.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___397_22984.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___397_22984.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___397_22984.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___397_22984.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___397_22984.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___397_22984.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___397_22984.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___397_22984.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___397_22984.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___397_22984.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___397_22984.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___397_22984.FStar_TypeChecker_Env.nbe)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____22988 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____22988
                       | uu____22989 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env ->
    fun e ->
      let uu____23006 =
        let uu____23007 = FStar_Syntax_Subst.compress e in
        uu____23007.FStar_Syntax_Syntax.n in
      match uu____23006 with
      | FStar_Syntax_Syntax.Tm_bvar uu____23012 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____23017 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____23042 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs, t, uu____23058) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t, uu____23104) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____23111 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23111 with | ((uu____23122, t), uu____23124) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____23130 = FStar_Syntax_Util.unfold_lazy i in
          universe_of_aux env uu____23130
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____23133, (FStar_Util.Inl t, uu____23135), uu____23136) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____23183, (FStar_Util.Inr c, uu____23185), uu____23186) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____23234 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____23243;
             FStar_Syntax_Syntax.vars = uu____23244;_},
           us)
          ->
          let uu____23250 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23250 with
           | ((us', t), uu____23263) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____23269 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____23269)
                else
                  FStar_List.iter2
                    (fun u' ->
                       fun u ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____23285 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____23286 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x, uu____23296) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____23323 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____23323 with
           | (bs1, c1) ->
               let us =
                 FStar_List.map
                   (fun uu____23345 ->
                      match uu____23345 with
                      | (b, uu____23353) ->
                          let uu____23358 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____23358) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____23365 = universe_of_aux env res in
                 level_of_type env res uu____23365 in
               let u_c =
                 let uu____23369 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____23369 with
                 | FStar_Pervasives_Native.None -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____23373 = universe_of_aux env trepr in
                     level_of_type env trepr uu____23373 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____23488 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____23505 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____23544 ->
                let uu____23545 = universe_of_aux env hd3 in
                (uu____23545, args1)
            | FStar_Syntax_Syntax.Tm_name uu____23560 ->
                let uu____23561 = universe_of_aux env hd3 in
                (uu____23561, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____23576 ->
                let uu____23589 = universe_of_aux env hd3 in
                (uu____23589, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____23604 ->
                let uu____23611 = universe_of_aux env hd3 in
                (uu____23611, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____23626 ->
                let uu____23653 = universe_of_aux env hd3 in
                (uu____23653, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____23668 ->
                let uu____23675 = universe_of_aux env hd3 in
                (uu____23675, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____23690 ->
                let uu____23691 = universe_of_aux env hd3 in
                (uu____23691, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____23706 ->
                let uu____23721 = universe_of_aux env hd3 in
                (uu____23721, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____23736 ->
                let uu____23743 = universe_of_aux env hd3 in
                (uu____23743, args1)
            | FStar_Syntax_Syntax.Tm_type uu____23758 ->
                let uu____23759 = universe_of_aux env hd3 in
                (uu____23759, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____23774, hd4::uu____23776) ->
                let uu____23841 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____23841 with
                 | (uu____23858, uu____23859, hd5) ->
                     let uu____23877 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____23877 with
                      | (hd6, args2) -> type_of_head retry hd6 args2))
            | uu____23936 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e in
                let uu____23938 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____23938 with
                 | (hd4, args2) -> type_of_head false hd4 args2)
            | uu____23997 ->
                let uu____23998 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____23998 with
                 | (env1, uu____24022) ->
                     let env2 =
                       let uu___398_24028 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___398_24028.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___398_24028.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___398_24028.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___398_24028.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___398_24028.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___398_24028.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___398_24028.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___398_24028.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___398_24028.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___398_24028.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___398_24028.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___398_24028.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___398_24028.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___398_24028.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___398_24028.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___398_24028.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___398_24028.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___398_24028.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___398_24028.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___398_24028.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___398_24028.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___398_24028.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___398_24028.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___398_24028.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___398_24028.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___398_24028.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___398_24028.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___398_24028.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___398_24028.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___398_24028.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___398_24028.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___398_24028.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___398_24028.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___398_24028.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___398_24028.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___398_24028.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___398_24028.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___398_24028.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___398_24028.FStar_TypeChecker_Env.nbe)
                       } in
                     ((let uu____24030 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____24030
                       then
                         let uu____24031 =
                           let uu____24032 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____24032 in
                         let uu____24033 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____24031 uu____24033
                       else ());
                      (let uu____24035 = tc_term env2 hd3 in
                       match uu____24035 with
                       | (uu____24058,
                          { FStar_Syntax_Syntax.eff_name = uu____24059;
                            FStar_Syntax_Syntax.res_typ = t;
                            FStar_Syntax_Syntax.cflags = uu____24061;
                            FStar_Syntax_Syntax.comp_thunk = uu____24062;_},
                          g) ->
                           ((let uu____24076 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____24076
                               (fun a236 -> ()));
                            (t, args1))))) in
          let uu____24089 = type_of_head true hd1 args in
          (match uu____24089 with
           | (t, args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t in
               let uu____24135 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____24135 with
                | (bs, res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____24189 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____24189)))
      | FStar_Syntax_Syntax.Tm_match (uu____24192, hd1::uu____24194) ->
          let uu____24259 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____24259 with
           | (uu____24262, uu____24263, hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____24281, []) ->
          level_of_type_fail env e "empty match cases"
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env ->
    fun e ->
      let uu____24328 = universe_of_aux env e in
      level_of_type env e uu____24328
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders, FStar_TypeChecker_Env.env,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun tps ->
      let uu____24353 = tc_binders env tps in
      match uu____24353 with
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
      let uu____24407 =
        let uu____24408 = FStar_Syntax_Subst.compress t in
        uu____24408.FStar_Syntax_Syntax.n in
      match uu____24407 with
      | FStar_Syntax_Syntax.Tm_delayed uu____24413 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____24438 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____24443 = FStar_Syntax_Util.unfold_lazy i in
          type_of_well_typed_term env uu____24443
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____24445 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____24445
            (fun uu____24459 ->
               match uu____24459 with
               | (t1, uu____24467) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____24469;
             FStar_Syntax_Syntax.vars = uu____24470;_},
           us)
          ->
          let uu____24476 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____24476
            (fun uu____24490 ->
               match uu____24490 with
               | (t1, uu____24498) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____24500 = tc_constant env t.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____24500
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____24502 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____24502
      | FStar_Syntax_Syntax.Tm_abs
          (bs, body, FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____24507;_})
          ->
          let mk_comp =
            let uu____24551 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid in
            if uu____24551
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____24579 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid in
               if uu____24579
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None) in
          FStar_Util.bind_opt mk_comp
            (fun f ->
               let uu____24646 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____24646
                 (fun u ->
                    let uu____24654 =
                      let uu____24657 =
                        let uu____24664 =
                          let uu____24665 =
                            let uu____24680 =
                              f tbody (FStar_Pervasives_Native.Some u) in
                            (bs, uu____24680) in
                          FStar_Syntax_Syntax.Tm_arrow uu____24665 in
                        FStar_Syntax_Syntax.mk uu____24664 in
                      uu____24657 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____24654))
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____24720 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____24720 with
           | (bs1, c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____24779 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____24779
                       (fun uc ->
                          let uu____24787 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____24787)
                 | (x, imp)::bs3 ->
                     let uu____24813 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____24813
                       (fun u_x ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____24822 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x, uu____24842) ->
          let uu____24847 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____24847
            (fun u_x ->
               let uu____24855 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____24855)
      | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
          let t_hd = type_of_well_typed_term env hd1 in
          let rec aux t_hd1 =
            let uu____24901 =
              let uu____24902 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____24902.FStar_Syntax_Syntax.n in
            match uu____24901 with
            | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____24984 = FStar_Util.first_N n_args bs in
                    match uu____24984 with
                    | (bs1, rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____25076 =
                          let uu____25081 = FStar_Syntax_Syntax.mk_Total t1 in
                          FStar_Syntax_Subst.open_comp bs1 uu____25081 in
                        (match uu____25076 with
                         | (bs2, c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____25141 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____25141 with
                       | (bs1, c1) ->
                           let uu____25162 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____25162
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____25240 ->
                     match uu____25240 with
                     | (bs1, t1) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b ->
                                fun a ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____25316 = FStar_Syntax_Subst.subst subst1 t1 in
                         FStar_Pervasives_Native.Some uu____25316)
            | FStar_Syntax_Syntax.Tm_refine (x, uu____25318) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____25324, uu____25325)
                -> aux t1
            | uu____25366 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25367, (FStar_Util.Inl t1, uu____25369), uu____25370) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25417, (FStar_Util.Inr c, uu____25419), uu____25420) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let uu____25485 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ in
          FStar_Pervasives_Native.Some uu____25485
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1, uu____25493) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____25498 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____25521 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____25534 ->
          FStar_Pervasives_Native.None
and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____25545 = type_of_well_typed_term env t in
      match uu____25545 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____25551;
            FStar_Syntax_Syntax.vars = uu____25552;_}
          -> FStar_Pervasives_Native.Some u
      | uu____25555 -> FStar_Pervasives_Native.None
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
            let uu___399_25580 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___399_25580.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___399_25580.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___399_25580.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___399_25580.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___399_25580.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___399_25580.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___399_25580.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___399_25580.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___399_25580.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___399_25580.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___399_25580.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___399_25580.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___399_25580.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___399_25580.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___399_25580.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___399_25580.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___399_25580.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___399_25580.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___399_25580.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___399_25580.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___399_25580.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___399_25580.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___399_25580.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___399_25580.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___399_25580.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___399_25580.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___399_25580.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___399_25580.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___399_25580.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___399_25580.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___399_25580.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___399_25580.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___399_25580.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___399_25580.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___399_25580.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___399_25580.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___399_25580.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___399_25580.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___399_25580.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___399_25580.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___399_25580.FStar_TypeChecker_Env.nbe)
            } in
          let slow_check uu____25586 =
            if must_total
            then
              let uu____25587 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____25587 with | (uu____25594, uu____25595, g) -> g
            else
              (let uu____25598 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____25598 with | (uu____25605, uu____25606, g) -> g) in
          let uu____25608 = type_of_well_typed_term env2 t in
          match uu____25608 with
          | FStar_Pervasives_Native.None -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____25613 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits") in
                if uu____25613
                then
                  let uu____25614 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                  let uu____25615 = FStar_Syntax_Print.term_to_string t in
                  let uu____25616 = FStar_Syntax_Print.term_to_string k' in
                  let uu____25617 = FStar_Syntax_Print.term_to_string k in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____25614 uu____25615 uu____25616 uu____25617
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k in
                (let uu____25623 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits") in
                 if uu____25623
                 then
                   let uu____25624 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
                   let uu____25625 = FStar_Syntax_Print.term_to_string t in
                   let uu____25626 = FStar_Syntax_Print.term_to_string k' in
                   let uu____25627 = FStar_Syntax_Print.term_to_string k in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____25624
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____25625 uu____25626 uu____25627
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
            let uu___400_25653 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___400_25653.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___400_25653.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___400_25653.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___400_25653.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___400_25653.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___400_25653.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___400_25653.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___400_25653.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___400_25653.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___400_25653.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___400_25653.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___400_25653.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___400_25653.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___400_25653.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___400_25653.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___400_25653.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___400_25653.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___400_25653.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___400_25653.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___400_25653.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___400_25653.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___400_25653.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___400_25653.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___400_25653.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___400_25653.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___400_25653.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___400_25653.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___400_25653.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___400_25653.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___400_25653.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___400_25653.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___400_25653.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___400_25653.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___400_25653.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___400_25653.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___400_25653.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___400_25653.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___400_25653.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___400_25653.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___400_25653.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___400_25653.FStar_TypeChecker_Env.nbe)
            } in
          let slow_check uu____25659 =
            if must_total
            then
              let uu____25660 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____25660 with | (uu____25667, uu____25668, g) -> g
            else
              (let uu____25671 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____25671 with | (uu____25678, uu____25679, g) -> g) in
          let uu____25681 =
            let uu____25682 = FStar_Options.__temp_fast_implicits () in
            FStar_All.pipe_left Prims.op_Negation uu____25682 in
          if uu____25681
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k