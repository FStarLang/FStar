open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___340_6 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___340_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___340_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___340_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___340_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___340_6.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___340_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___340_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___340_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___340_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___340_6.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___340_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___340_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___340_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___340_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___340_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___340_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___340_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___340_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___340_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___340_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___340_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___340_6.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___340_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___340_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___340_6.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___340_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___340_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___340_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___340_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___340_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___340_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___340_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___340_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___340_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___340_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___340_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___340_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___340_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___340_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___340_6.FStar_TypeChecker_Env.dep_graph);
      FStar_TypeChecker_Env.nbe = (uu___340_6.FStar_TypeChecker_Env.nbe)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___341_12 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___341_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___341_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___341_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___341_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___341_12.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___341_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___341_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___341_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___341_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___341_12.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___341_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___341_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___341_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___341_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___341_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___341_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___341_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___341_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___341_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___341_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___341_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___341_12.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___341_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___341_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___341_12.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___341_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___341_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___341_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___341_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___341_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___341_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___341_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___341_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___341_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___341_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___341_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___341_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___341_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___341_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___341_12.FStar_TypeChecker_Env.dep_graph);
      FStar_TypeChecker_Env.nbe = (uu___341_12.FStar_TypeChecker_Env.nbe)
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
           let uu____46 =
             let uu____51 =
               let uu____52 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____61 =
                 let uu____72 = FStar_Syntax_Syntax.as_arg tl1  in [uu____72]
                  in
               uu____52 :: uu____61  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____51
              in
           uu____46 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___334_113  ->
    match uu___334_113 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____116 -> false
  
let steps :
  'Auu____123 . 'Auu____123 -> FStar_TypeChecker_Env.step Prims.list =
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
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____206 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____218 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____218 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____242 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____244 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____244
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____246 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____247 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____246 uu____247
                             in
                          let uu____248 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____248
                           in
                        let uu____253 =
                          let uu____266 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____267 =
                            let uu____268 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____268
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____266 env uu____267
                           in
                        match uu____253 with
                        | (s,uu____282,g0) ->
                            let uu____296 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____296 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____305 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____305
                                    in
                                 (s, g1)
                             | uu____306 -> fail1 ())))
             in
          aux false kt
  
let push_binding :
  'Auu____315 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____315) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____369 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____369
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
        (fun uu____391  ->
           let uu____392 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____392 t)
  
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
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
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
                 let uu____448 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                   uu____448
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_Syntax_Syntax.res_typ  in
           let uu____451 =
             let uu____458 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____458 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____468 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t'
                    in
                 (match uu____468 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____482 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____482 with
                       | (e2,g) ->
                           ((let uu____496 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____496
                             then
                               let uu____497 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____498 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____499 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____500 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____497 uu____498 uu____499 uu____500
                             else ());
                            (let msg =
                               let uu____508 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g
                                  in
                               if uu____508
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_16  ->
                                      FStar_Pervasives_Native.Some _0_16)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard  in
                             let uu____530 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1
                                in
                             match uu____530 with
                             | (lc2,g2) ->
                                 let uu____543 = set_lcomp_result lc2 t'  in
                                 ((memo_tk e2 t'), uu____543, g2)))))
              in
           match uu____451 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____580 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____580 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____590 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____590 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____642 = ec  in
        match uu____642 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____665 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____665
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____667 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____667
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____669 =
              match copt with
              | FStar_Pervasives_Native.Some uu____682 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
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
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____687))
                     in
                  if uu____685
                  then
                    let uu____694 =
                      let uu____697 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____697  in
                    (uu____694, c)
                  else
                    (let uu____701 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____701
                     then
                       let uu____708 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____708)
                     else
                       (let uu____712 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____712
                        then
                          let uu____719 =
                            let uu____722 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____722  in
                          (uu____719, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____669 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____749 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____749
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____752 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low
                           in
                        if uu____752
                        then
                          let uu____753 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____754 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____755 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____753 uu____754 uu____755
                        else ());
                       (let uu____757 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____757 with
                        | (e1,uu____771,g) ->
                            let g1 =
                              let uu____774 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____774
                                "could not prove post-condition" g
                               in
                            ((let uu____776 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____776
                              then
                                let uu____777 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____778 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____777 uu____778
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
  'Auu____789 'Auu____790 .
    FStar_TypeChecker_Env.env ->
      ('Auu____789,'Auu____790,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____789,'Auu____790,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____812  ->
      match uu____812 with
      | (te,kt,f) ->
          let uu____822 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____822 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____830 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____835 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____830 uu____835)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____847 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____847 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____851 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____851
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____888 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____888 with
        | (head1,args) ->
            let uu____933 =
              let uu____948 =
                let uu____949 = FStar_Syntax_Util.un_uinst head1  in
                uu____949.FStar_Syntax_Syntax.n  in
              (uu____948, args)  in
            (match uu____933 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____965) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____990,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____991))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1064,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1065))::(pat,FStar_Pervasives_Native.None
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
             | uu____1147 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1176 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____1176)
            FStar_Pervasives_Native.tuple2 Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1212 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1219 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1212 uu____1219  in
          let uu____1220 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1247  ->
                    match uu____1247 with
                    | (b,uu____1253) ->
                        let uu____1254 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1254))
             in
          match uu____1220 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1260) ->
              let uu____1265 =
                let uu____1270 =
                  let uu____1271 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1271
                   in
                (FStar_Errors.Warning_PatternMissingBoundVar, uu____1270)  in
              FStar_Errors.log_issue rng uu____1265
  
let check_smt_pat :
  'Auu____1282 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,'Auu____1282) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____1323 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____1323
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____1324;
                  FStar_Syntax_Syntax.effect_name = uu____1325;
                  FStar_Syntax_Syntax.result_typ = uu____1326;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____1330)::[];
                  FStar_Syntax_Syntax.flags = uu____1331;_}
                -> check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs
            | uu____1392 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
          FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___342_1452 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___342_1452.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___342_1452.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___342_1452.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___342_1452.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___342_1452.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___342_1452.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___342_1452.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___342_1452.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___342_1452.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___342_1452.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___342_1452.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___342_1452.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___342_1452.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___342_1452.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___342_1452.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___342_1452.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___342_1452.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___342_1452.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___342_1452.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___342_1452.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___342_1452.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___342_1452.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___342_1452.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___342_1452.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___342_1452.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___342_1452.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___342_1452.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___342_1452.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___342_1452.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___342_1452.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___342_1452.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___342_1452.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___342_1452.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___342_1452.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___342_1452.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___342_1452.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___342_1452.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___342_1452.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___342_1452.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___342_1452.FStar_TypeChecker_Env.dep_graph);
                FStar_TypeChecker_Env.nbe =
                  (uu___342_1452.FStar_TypeChecker_Env.nbe)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____1478 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____1478
               then
                 let uu____1479 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____1480 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____1479 uu____1480
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____1511  ->
                         match uu____1511 with
                         | (b,uu____1521) ->
                             let t =
                               let uu____1527 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____1527
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____1530 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____1531 -> []
                              | uu____1546 ->
                                  let uu____1547 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____1547])))
                  in
               let as_lex_list dec =
                 let uu____1560 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____1560 with
                 | (head1,uu____1580) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1608 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____1616 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___335_1625  ->
                         match uu___335_1625 with
                         | FStar_Syntax_Syntax.DECREASES uu____1626 -> true
                         | uu____1629 -> false))
                  in
               match uu____1616 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1635 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____1656 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1685 =
              match uu____1685 with
              | (l,t,u_names) ->
                  let uu____1709 =
                    let uu____1710 = FStar_Syntax_Subst.compress t  in
                    uu____1710.FStar_Syntax_Syntax.n  in
                  (match uu____1709 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1769  ->
                                 match uu____1769 with
                                 | (x,imp) ->
                                     let uu____1788 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1788
                                     then
                                       let uu____1795 =
                                         let uu____1796 =
                                           let uu____1799 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1799
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1796
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1795, imp)
                                     else (x, imp)))
                          in
                       let uu____1805 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1805 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1826 =
                                let uu____1831 =
                                  let uu____1832 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1841 =
                                    let uu____1852 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1852]  in
                                  uu____1832 :: uu____1841  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1831
                                 in
                              uu____1826 FStar_Pervasives_Native.None r  in
                            let uu____1887 = FStar_Util.prefix formals2  in
                            (match uu____1887 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___343_1950 = last1  in
                                   let uu____1951 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___343_1950.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___343_1950.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1951
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____1987 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1987
                                   then
                                     let uu____1988 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1989 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1990 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1988 uu____1989 uu____1990
                                   else ());
                                  (l, t', u_names))))
                   | uu____1994 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____2644 =
        FStar_Util.record_time
          (fun uu____2662  ->
             tc_maybe_toplevel_term
               (let uu___344_2665 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___344_2665.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___344_2665.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___344_2665.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___344_2665.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___344_2665.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___344_2665.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___344_2665.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___344_2665.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___344_2665.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___344_2665.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___344_2665.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___344_2665.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___344_2665.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___344_2665.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___344_2665.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level = false;
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___344_2665.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___344_2665.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___344_2665.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___344_2665.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___344_2665.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___344_2665.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___344_2665.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___344_2665.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___344_2665.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___344_2665.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___344_2665.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___344_2665.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___344_2665.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___344_2665.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___344_2665.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___344_2665.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___344_2665.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___344_2665.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___344_2665.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___344_2665.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___344_2665.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___344_2665.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___344_2665.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___344_2665.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___344_2665.FStar_TypeChecker_Env.dep_graph);
                  FStar_TypeChecker_Env.nbe =
                    (uu___344_2665.FStar_TypeChecker_Env.nbe)
                }) e)
         in
      match uu____2644 with
      | (r,ms) ->
          ((let uu____2687 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____2687
            then
              let uu____2688 =
                let uu____2689 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left FStar_Range.string_of_range uu____2689
                 in
              let uu____2690 = FStar_Syntax_Print.term_to_string e  in
              let uu____2691 =
                let uu____2692 = FStar_Syntax_Subst.compress e  in
                FStar_Syntax_Print.tag_of_term uu____2692  in
              let uu____2693 = FStar_Util.string_of_int ms  in
              FStar_Util.print4 "(%s) tc_term of %s (%s) took %sms\n"
                uu____2688 uu____2690 uu____2691 uu____2693
            else ());
           r)

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____2707 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2707
       then
         let uu____2708 =
           let uu____2709 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2709  in
         let uu____2710 = FStar_Syntax_Print.tag_of_term top  in
         let uu____2711 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2708 uu____2710
           uu____2711
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2719 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2748 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2755 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2768 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2769 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2770 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2771 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2772 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2791 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2806 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2813 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted
           (uu____2814,{
                         FStar_Syntax_Syntax.qkind =
                           FStar_Syntax_Syntax.Quote_static ;
                         FStar_Syntax_Syntax.antiquotes = aqs;_})
           when
           FStar_List.for_all
             (fun uu____2842  ->
                match uu____2842 with
                | (uu____2851,b,uu____2853) -> Prims.op_Negation b) aqs
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_quoted uu____2858 ->
           let c =
             FStar_Syntax_Syntax.mk_Comp
               {
                 FStar_Syntax_Syntax.comp_univs =
                   [FStar_Syntax_Syntax.U_zero];
                 FStar_Syntax_Syntax.effect_name =
                   FStar_Parser_Const.effect_Tac_lid;
                 FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term;
                 FStar_Syntax_Syntax.effect_args = [];
                 FStar_Syntax_Syntax.flags =
                   [FStar_Syntax_Syntax.SOMETRIVIAL;
                   FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
               }
              in
           let uu____2874 =
             let uu____2881 =
               let uu____2886 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____2886  in
             value_check_expected_typ env1 top uu____2881
               FStar_TypeChecker_Env.trivial_guard
              in
           (match uu____2874 with
            | (t,lc,g) ->
                let t1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (t,
                         (FStar_Syntax_Syntax.Meta_monadic_lift
                            (FStar_Parser_Const.effect_PURE_lid,
                              FStar_Parser_Const.effect_TAC_lid,
                              FStar_Syntax_Syntax.t_term))))
                    FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                   in
                (t1, lc, g))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____2903;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____2904;
             FStar_Syntax_Syntax.ltyp = uu____2905;
             FStar_Syntax_Syntax.rng = uu____2906;_}
           ->
           let uu____2917 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____2917
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____2924 = tc_tot_or_gtot_term env1 e1  in
           (match uu____2924 with
            | (e2,c,g) ->
                let g1 =
                  let uu___345_2941 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___345_2941.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___345_2941.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___345_2941.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____2942 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____2942, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2963 = FStar_Syntax_Util.type_u ()  in
           (match uu____2963 with
            | (t,u) ->
                let uu____2976 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____2976 with
                 | (e2,c,g) ->
                     let uu____2992 =
                       let uu____3009 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____3009 with
                       | (env2,uu____3033) -> tc_pats env2 pats  in
                     (match uu____2992 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___346_3071 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___346_3071.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___346_3071.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___346_3071.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____3072 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____3075 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____3072, c, uu____3075))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____3081 =
             let uu____3082 = FStar_Syntax_Subst.compress e1  in
             uu____3082.FStar_Syntax_Syntax.n  in
           (match uu____3081 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____3091,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____3093;
                               FStar_Syntax_Syntax.lbtyp = uu____3094;
                               FStar_Syntax_Syntax.lbeff = uu____3095;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____3097;
                               FStar_Syntax_Syntax.lbpos = uu____3098;_}::[]),e2)
                ->
                let uu____3126 =
                  let uu____3133 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____3133 e11  in
                (match uu____3126 with
                 | (e12,c1,g1) ->
                     let uu____3143 = tc_term env1 e2  in
                     (match uu____3143 with
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
                          let e3 =
                            let uu____3167 =
                              let uu____3174 =
                                let uu____3175 =
                                  let uu____3188 =
                                    let uu____3195 =
                                      let uu____3198 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____3198]  in
                                    (false, uu____3195)  in
                                  (uu____3188, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____3175  in
                              FStar_Syntax_Syntax.mk uu____3174  in
                            uu____3167 FStar_Pervasives_Native.None
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
                          let uu____3220 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____3220)))
            | uu____3221 ->
                let uu____3222 = tc_term env1 e1  in
                (match uu____3222 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____3244) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____3256) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____3275 = tc_term env1 e1  in
           (match uu____3275 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____3299) ->
           let uu____3346 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____3346 with
            | (env0,uu____3360) ->
                let uu____3365 = tc_comp env0 expected_c  in
                (match uu____3365 with
                 | (expected_c1,uu____3379,g) ->
                     let uu____3381 =
                       let uu____3388 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____3388 e1  in
                     (match uu____3381 with
                      | (e2,c',g') ->
                          let uu____3398 =
                            let uu____3405 =
                              let uu____3410 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____3410)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____3405
                             in
                          (match uu____3398 with
                           | (e3,expected_c2,g'') ->
                               let topt1 = tc_tactic_opt env0 topt  in
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2), topt1),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2
                                  in
                               let f =
                                 let uu____3464 =
                                   FStar_TypeChecker_Env.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Env.conj_guard g
                                   uu____3464
                                  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Env.map_guard f
                                       (fun f1  ->
                                          let uu____3470 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____3470)
                                  in
                               let uu____3471 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____3471 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Env.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____3491) ->
           let uu____3538 = FStar_Syntax_Util.type_u ()  in
           (match uu____3538 with
            | (k,u) ->
                let uu____3551 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____3551 with
                 | (t1,uu____3565,f) ->
                     let uu____3567 =
                       let uu____3574 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____3574 e1  in
                     (match uu____3567 with
                      | (e2,c,g) ->
                          let uu____3584 =
                            let uu____3589 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____3594  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____3589 e2 c f
                             in
                          (match uu____3584 with
                           | (c1,f1) ->
                               let uu____3603 =
                                 let uu____3610 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos
                                    in
                                 comp_check_expected_typ env1 uu____3610 c1
                                  in
                               (match uu____3603 with
                                | (e3,c2,f2) ->
                                    let uu____3658 =
                                      let uu____3659 =
                                        FStar_TypeChecker_Env.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____3659
                                       in
                                    (e3, c2, uu____3658))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3660;
              FStar_Syntax_Syntax.vars = uu____3661;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3740 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3740 with
            | (unary_op1,uu____3764) ->
                let head1 =
                  let uu____3792 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____3792
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
              FStar_Syntax_Syntax.pos = uu____3840;
              FStar_Syntax_Syntax.vars = uu____3841;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3920 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3920 with
            | (unary_op1,uu____3944) ->
                let head1 =
                  let uu____3972 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____3972
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
                (FStar_Const.Const_reflect uu____4020);
              FStar_Syntax_Syntax.pos = uu____4021;
              FStar_Syntax_Syntax.vars = uu____4022;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4101 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4101 with
            | (unary_op1,uu____4125) ->
                let head1 =
                  let uu____4153 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4153
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
              FStar_Syntax_Syntax.pos = uu____4201;
              FStar_Syntax_Syntax.vars = uu____4202;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4298 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4298 with
            | (unary_op1,uu____4322) ->
                let head1 =
                  let uu____4350 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____4350
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
              FStar_Syntax_Syntax.pos = uu____4406;
              FStar_Syntax_Syntax.vars = uu____4407;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____4445 =
             let uu____4452 =
               let uu____4453 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4453  in
             tc_term uu____4452 e1  in
           (match uu____4445 with
            | (e2,c,g) ->
                let uu____4477 = FStar_Syntax_Util.head_and_args top  in
                (match uu____4477 with
                 | (head1,uu____4501) ->
                     let uu____4526 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____4559 =
                       let uu____4560 =
                         let uu____4561 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____4561  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4560
                        in
                     (uu____4526, uu____4559, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4562;
              FStar_Syntax_Syntax.vars = uu____4563;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____4616 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4616 with
            | (head1,uu____4640) ->
                let env' =
                  let uu____4666 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____4666  in
                let uu____4667 = tc_term env' r  in
                (match uu____4667 with
                 | (er,uu____4681,gr) ->
                     let uu____4683 = tc_term env1 t  in
                     (match uu____4683 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____4700 =
                            let uu____4701 =
                              let uu____4706 =
                                let uu____4707 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____4716 =
                                  let uu____4727 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____4727]  in
                                uu____4707 :: uu____4716  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____4706
                               in
                            uu____4701 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____4700, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____4762;
              FStar_Syntax_Syntax.vars = uu____4763;_},uu____4764)
           ->
           let uu____4789 =
             let uu____4794 =
               let uu____4795 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4795  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4794)  in
           FStar_Errors.raise_error uu____4789 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4802;
              FStar_Syntax_Syntax.vars = uu____4803;_},uu____4804)
           ->
           let uu____4829 =
             let uu____4834 =
               let uu____4835 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4835  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4834)  in
           FStar_Errors.raise_error uu____4829 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____4842;
              FStar_Syntax_Syntax.vars = uu____4843;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____4886 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____4886 with
             | (env0,uu____4900) ->
                 let uu____4905 = tc_term env0 e1  in
                 (match uu____4905 with
                  | (e2,c,g) ->
                      let uu____4921 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____4921 with
                       | (reify_op,uu____4945) ->
                           let u_c =
                             let uu____4971 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____4971 with
                             | (uu____4978,c',uu____4980) ->
                                 let uu____4981 =
                                   let uu____4982 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____4982.FStar_Syntax_Syntax.n  in
                                 (match uu____4981 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____4986 ->
                                      let uu____4987 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____4987 with
                                       | (t,u) ->
                                           let g_opt =
                                             FStar_TypeChecker_Rel.try_teq
                                               true env1
                                               c'.FStar_Syntax_Syntax.res_typ
                                               t
                                              in
                                           ((match g_opt with
                                             | FStar_Pervasives_Native.Some
                                                 g' ->
                                                 FStar_TypeChecker_Rel.force_trivial_guard
                                                   env1 g'
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 let uu____4999 =
                                                   let uu____5000 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____5001 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____5002 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____5000 uu____5001
                                                     uu____5002
                                                    in
                                                 failwith uu____4999);
                                            u)))
                              in
                           let repr =
                             let uu____5004 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____5004
                               u_c
                              in
                           let e3 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app
                                  (reify_op, [(e2, aqual)]))
                               FStar_Pervasives_Native.None
                               top.FStar_Syntax_Syntax.pos
                              in
                           let c1 =
                             let uu____5041 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____5041
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____5042 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____5042 with
                            | (e4,c2,g') ->
                                let uu____5058 =
                                  FStar_TypeChecker_Env.conj_guard g g'  in
                                (e4, c2, uu____5058))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____5060;
              FStar_Syntax_Syntax.vars = uu____5061;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____5115 =
               let uu____5116 =
                 let uu____5121 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____5121)  in
               FStar_Errors.raise_error uu____5116 e1.FStar_Syntax_Syntax.pos
                in
             let uu____5128 = FStar_Syntax_Util.head_and_args top  in
             match uu____5128 with
             | (reflect_op,uu____5152) ->
                 let uu____5177 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____5177 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____5210 =
                        let uu____5211 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____5211  in
                      if uu____5210
                      then no_reflect ()
                      else
                        (let uu____5221 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____5221 with
                         | (env_no_ex,topt) ->
                             let uu____5240 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____5260 =
                                   let uu____5267 =
                                     let uu____5268 =
                                       let uu____5285 =
                                         let uu____5296 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____5305 =
                                           let uu____5316 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____5316]  in
                                         uu____5296 :: uu____5305  in
                                       (repr, uu____5285)  in
                                     FStar_Syntax_Syntax.Tm_app uu____5268
                                      in
                                   FStar_Syntax_Syntax.mk uu____5267  in
                                 uu____5260 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____5364 =
                                 let uu____5371 =
                                   let uu____5372 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____5372
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____5371 t  in
                               match uu____5364 with
                               | (t1,uu____5398,g) ->
                                   let uu____5400 =
                                     let uu____5401 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____5401.FStar_Syntax_Syntax.n  in
                                   (match uu____5400 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____5414,(res,uu____5416)::
                                         (wp,uu____5418)::[])
                                        -> (t1, res, wp, g)
                                    | uu____5475 -> failwith "Impossible")
                                in
                             (match uu____5240 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____5500 =
                                    let uu____5507 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____5507 with
                                    | (e2,c,g) ->
                                        ((let uu____5524 =
                                            let uu____5525 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____5525
                                             in
                                          if uu____5524
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____5539 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____5539 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____5549 =
                                                  let uu____5558 =
                                                    let uu____5565 =
                                                      let uu____5566 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____5567 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____5566 uu____5567
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____5565,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____5558]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____5549);
                                               (let uu____5580 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____5580)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____5584 =
                                                let uu____5585 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g' uu____5585
                                                 in
                                              (e2, uu____5584)))
                                     in
                                  (match uu____5500 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____5601 =
                                           let uu____5602 =
                                             let uu____5603 =
                                               let uu____5604 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____5604]  in
                                             let uu____5605 =
                                               let uu____5616 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____5616]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____5603;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____5605;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____5602
                                            in
                                         FStar_All.pipe_right uu____5601
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____5676 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____5676 with
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
                                            let uu____5699 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g' g
                                               in
                                            (e5, c1, uu____5699))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5738 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5738 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____5788,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____5789))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5841 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5841 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5916 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____6125 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____5916 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____6242 =
               let uu____6243 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____6243 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____6242 instantiate_both  in
           ((let uu____6259 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____6259
             then
               let uu____6260 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____6261 = FStar_Syntax_Print.term_to_string top  in
               let uu____6262 =
                 let uu____6263 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____6263
                   (fun uu___336_6269  ->
                      match uu___336_6269 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____6260
                 uu____6261 uu____6262
             else ());
            (let uu____6274 = tc_term (no_inst env2) head1  in
             match uu____6274 with
             | (head2,chead,g_head) ->
                 let uu____6290 =
                   let uu____6297 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____6299 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____6299))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____6297
                   then
                     let uu____6306 =
                       let uu____6313 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____6313
                        in
                     match uu____6306 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____6326 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____6326)
                    in
                 (match uu____6290 with
                  | (e1,c,g) ->
                      let uu____6338 =
                        let uu____6345 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____6345
                        then
                          let uu____6352 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____6352 with
                          | (e2,res_typ,implicits) ->
                              let uu____6368 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____6368, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____6338 with
                       | (e2,c1,implicits) ->
                           ((let uu____6380 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____6380
                             then
                               let uu____6381 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____6381
                             else ());
                            (let uu____6383 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____6383 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____6402 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____6402
                                   then
                                     let uu____6403 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____6404 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____6403 uu____6404
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____6444 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____6444 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____6464 = tc_term env12 e1  in
                (match uu____6464 with
                 | (e11,c1,g1) ->
                     let uu____6480 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____6494 = FStar_Syntax_Util.type_u ()  in
                           (match uu____6494 with
                            | (k,uu____6506) ->
                                let uu____6507 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____6507 with
                                 | (res_t,uu____6527,g) ->
                                     let uu____6541 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____6542 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____6541, res_t, uu____6542)))
                        in
                     (match uu____6480 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____6553 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____6553
                            then
                              let uu____6554 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____6554
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
                            let uu____6675 =
                              let uu____6680 =
                                FStar_List.fold_right
                                  (fun uu____6759  ->
                                     fun uu____6760  ->
                                       match (uu____6759, uu____6760) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____6994 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____6994)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____6680 with
                              | (cases,g) ->
                                  let uu____7092 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____7092, g)
                               in
                            match uu____6675 with
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
                                           (fun uu____7232  ->
                                              match uu____7232 with
                                              | ((pat,wopt,br),uu____7276,eff_label,uu____7278,uu____7279,uu____7280)
                                                  ->
                                                  let uu____7315 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____7315)))
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
                                  let uu____7382 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____7382
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____7387 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____7387  in
                                     let lb =
                                       let uu____7391 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____7391 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____7397 =
                                         let uu____7404 =
                                           let uu____7405 =
                                             let uu____7418 =
                                               let uu____7421 =
                                                 let uu____7422 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____7422]  in
                                               FStar_Syntax_Subst.close
                                                 uu____7421 e_match
                                                in
                                             ((false, [lb]), uu____7418)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____7405
                                            in
                                         FStar_Syntax_Syntax.mk uu____7404
                                          in
                                       uu____7397
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____7455 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____7455
                                  then
                                    let uu____7456 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7457 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____7456 uu____7457
                                  else ());
                                 (let uu____7459 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____7459))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7460;
                FStar_Syntax_Syntax.lbunivs = uu____7461;
                FStar_Syntax_Syntax.lbtyp = uu____7462;
                FStar_Syntax_Syntax.lbeff = uu____7463;
                FStar_Syntax_Syntax.lbdef = uu____7464;
                FStar_Syntax_Syntax.lbattrs = uu____7465;
                FStar_Syntax_Syntax.lbpos = uu____7466;_}::[]),uu____7467)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____7490),uu____7491) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7506;
                FStar_Syntax_Syntax.lbunivs = uu____7507;
                FStar_Syntax_Syntax.lbtyp = uu____7508;
                FStar_Syntax_Syntax.lbeff = uu____7509;
                FStar_Syntax_Syntax.lbdef = uu____7510;
                FStar_Syntax_Syntax.lbattrs = uu____7511;
                FStar_Syntax_Syntax.lbpos = uu____7512;_}::uu____7513),uu____7514)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____7539),uu____7540) ->
           check_inner_let_rec env1 top)

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun head1  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____7571 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____7610))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____7650 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____7571 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____7681 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____7681 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____7685 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____7685)
                 in
              let uu____7686 = FStar_TypeChecker_Env.clear_expected_typ env
                 in
              (match uu____7686 with
               | (env',uu____7700) ->
                   let uu____7705 = tc_term env' typ  in
                   (match uu____7705 with
                    | (typ1,uu____7719,g1) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                         (let uu____7722 = tc_tactic env' tau  in
                          match uu____7722 with
                          | (tau1,uu____7736,g2) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env'
                                 g2;
                               (let t =
                                  env.FStar_TypeChecker_Env.synth_hook env'
                                    typ1
                                    (let uu___347_7741 = tau1  in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (uu___347_7741.FStar_Syntax_Syntax.n);
                                       FStar_Syntax_Syntax.pos = rng;
                                       FStar_Syntax_Syntax.vars =
                                         (uu___347_7741.FStar_Syntax_Syntax.vars)
                                     })
                                   in
                                (let uu____7743 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Tac")
                                    in
                                 if uu____7743
                                 then
                                   let uu____7744 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   FStar_Util.print1 "Got %s\n" uu____7744
                                 else ());
                                FStar_TypeChecker_Util.check_uvars
                                  tau1.FStar_Syntax_Syntax.pos t;
                                (let uu____7747 =
                                   let uu____7748 =
                                     FStar_Syntax_Syntax.mk_Total typ1  in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.lcomp_of_comp
                                     uu____7748
                                    in
                                 (t, uu____7747,
                                   FStar_TypeChecker_Env.trivial_guard))))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___348_7752 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___348_7752.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___348_7752.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___348_7752.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___348_7752.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___348_7752.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___348_7752.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___348_7752.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___348_7752.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___348_7752.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___348_7752.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___348_7752.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___348_7752.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___348_7752.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___348_7752.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___348_7752.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___348_7752.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___348_7752.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___348_7752.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___348_7752.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___348_7752.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___348_7752.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___348_7752.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___348_7752.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___348_7752.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___348_7752.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___348_7752.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___348_7752.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___348_7752.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___348_7752.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___348_7752.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___348_7752.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___348_7752.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___348_7752.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___348_7752.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___348_7752.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___348_7752.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___348_7752.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___348_7752.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___348_7752.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___348_7752.FStar_TypeChecker_Env.dep_graph);
          FStar_TypeChecker_Env.nbe =
            (uu___348_7752.FStar_TypeChecker_Env.nbe)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and (tc_reified_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___349_7756 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___349_7756.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___349_7756.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___349_7756.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___349_7756.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___349_7756.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___349_7756.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___349_7756.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___349_7756.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___349_7756.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___349_7756.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___349_7756.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___349_7756.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___349_7756.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___349_7756.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___349_7756.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___349_7756.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___349_7756.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___349_7756.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___349_7756.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___349_7756.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___349_7756.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___349_7756.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___349_7756.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___349_7756.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___349_7756.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___349_7756.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___349_7756.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___349_7756.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___349_7756.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___349_7756.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___349_7756.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___349_7756.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___349_7756.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___349_7756.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___349_7756.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___349_7756.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___349_7756.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___349_7756.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___349_7756.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___349_7756.FStar_TypeChecker_Env.dep_graph);
          FStar_TypeChecker_Env.nbe =
            (uu___349_7756.FStar_TypeChecker_Env.nbe)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____7772 = tc_tactic env tactic  in
          (match uu____7772 with
           | (tactic1,uu____7782,uu____7783) ->
               FStar_Pervasives_Native.Some tactic1)

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____7832 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____7832 with
        | (e2,t,implicits) ->
            let tc =
              let uu____7853 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____7853
              then FStar_Util.Inl t
              else
                (let uu____7859 =
                   let uu____7860 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____7860
                    in
                 FStar_Util.Inr uu____7859)
               in
            let is_data_ctor uu___337_7868 =
              match uu___337_7868 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____7871) -> true
              | uu____7878 -> false  in
            let uu____7881 =
              (is_data_ctor dc) &&
                (let uu____7883 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____7883)
               in
            if uu____7881
            then
              let uu____7890 =
                let uu____7895 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____7895)  in
              let uu____7896 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____7890 uu____7896
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____7913 =
            let uu____7914 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____7914
             in
          failwith uu____7913
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____7939 =
            let uu____7944 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____7944  in
          value_check_expected_typ env1 e uu____7939
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____7946 =
            let uu____7959 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____7959 with
            | FStar_Pervasives_Native.None  ->
                let uu____7974 = FStar_Syntax_Util.type_u ()  in
                (match uu____7974 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____7946 with
           | (t,uu____8011,g0) ->
               let uu____8025 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____8025 with
                | (e1,uu____8045,g1) ->
                    let uu____8059 =
                      let uu____8060 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____8060
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____8061 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____8059, uu____8061)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____8063 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____8072 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____8072)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____8063 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___350_8085 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___350_8085.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___350_8085.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____8088 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____8088 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____8109 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____8109
                       then FStar_Util.Inl t1
                       else
                         (let uu____8115 =
                            let uu____8116 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____8116
                             in
                          FStar_Util.Inr uu____8115)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8118;
             FStar_Syntax_Syntax.vars = uu____8119;_},uu____8120)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8125 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8125
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8133 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8133
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8141;
             FStar_Syntax_Syntax.vars = uu____8142;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____8151 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8151 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____8174 =
                     let uu____8179 =
                       let uu____8180 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____8181 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____8182 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____8180 uu____8181 uu____8182
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____8179)
                      in
                   let uu____8183 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____8174 uu____8183)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____8199 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8203 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8203 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8205 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8205 with
           | ((us,t),range) ->
               ((let uu____8228 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____8228
                 then
                   let uu____8229 =
                     let uu____8230 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____8230  in
                   let uu____8231 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____8232 = FStar_Range.string_of_range range  in
                   let uu____8233 = FStar_Range.string_of_use_range range  in
                   let uu____8234 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____8229 uu____8231 uu____8232 uu____8233 uu____8234
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8239 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8239 us  in
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
          let uu____8267 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8267 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____8281 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8281 with
                | (env2,uu____8295) ->
                    let uu____8300 = tc_binders env2 bs1  in
                    (match uu____8300 with
                     | (bs2,env3,g,us) ->
                         let uu____8319 = tc_comp env3 c1  in
                         (match uu____8319 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___351_8338 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___351_8338.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___351_8338.FStar_Syntax_Syntax.vars)
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
                                  let uu____8349 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____8349
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
          let uu____8365 =
            let uu____8370 =
              let uu____8371 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8371]  in
            FStar_Syntax_Subst.open_term uu____8370 phi  in
          (match uu____8365 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____8399 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8399 with
                | (env2,uu____8413) ->
                    let uu____8418 =
                      let uu____8433 = FStar_List.hd x1  in
                      tc_binder env2 uu____8433  in
                    (match uu____8418 with
                     | (x2,env3,f1,u) ->
                         ((let uu____8469 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____8469
                           then
                             let uu____8470 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____8471 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____8472 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____8470 uu____8471 uu____8472
                           else ());
                          (let uu____8476 = FStar_Syntax_Util.type_u ()  in
                           match uu____8476 with
                           | (t_phi,uu____8488) ->
                               let uu____8489 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____8489 with
                                | (phi2,uu____8503,f2) ->
                                    let e1 =
                                      let uu___352_8508 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___352_8508.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___352_8508.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____8517 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____8517
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____8545) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____8572 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____8572
            then
              let uu____8573 =
                FStar_Syntax_Print.term_to_string
                  (let uu___353_8576 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___353_8576.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___353_8576.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____8573
            else ());
           (let uu____8590 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____8590 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____8603 ->
          let uu____8604 =
            let uu____8605 = FStar_Syntax_Print.term_to_string top  in
            let uu____8606 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____8605
              uu____8606
             in
          failwith uu____8604

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____8616 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____8617,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____8628,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____8644 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____8649 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____8650 ->
            let uu____8652 =
              let uu____8657 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____8657 FStar_Util.must  in
            FStar_All.pipe_right uu____8652 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____8682 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____8683 =
              let uu____8688 =
                let uu____8689 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8689
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8688)  in
            FStar_Errors.raise_error uu____8683 r
        | FStar_Const.Const_set_range_of  ->
            let uu____8690 =
              let uu____8695 =
                let uu____8696 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8696
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8695)  in
            FStar_Errors.raise_error uu____8690 r
        | FStar_Const.Const_reify  ->
            let uu____8697 =
              let uu____8702 =
                let uu____8703 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8703
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8702)  in
            FStar_Errors.raise_error uu____8697 r
        | FStar_Const.Const_reflect uu____8704 ->
            let uu____8705 =
              let uu____8710 =
                let uu____8711 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8711
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8710)  in
            FStar_Errors.raise_error uu____8705 r
        | uu____8712 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.universe,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____8729) ->
          let uu____8738 = FStar_Syntax_Util.type_u ()  in
          (match uu____8738 with
           | (k,u) ->
               let uu____8751 = tc_check_tot_or_gtot_term env t k  in
               (match uu____8751 with
                | (t1,uu____8765,g) ->
                    let uu____8767 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____8767, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____8769) ->
          let uu____8778 = FStar_Syntax_Util.type_u ()  in
          (match uu____8778 with
           | (k,u) ->
               let uu____8791 = tc_check_tot_or_gtot_term env t k  in
               (match uu____8791 with
                | (t1,uu____8805,g) ->
                    let uu____8807 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____8807, u, g)))
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
            let uu____8817 =
              let uu____8822 =
                let uu____8823 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____8823 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____8822  in
            uu____8817 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____8842 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____8842 with
           | (tc1,uu____8856,f) ->
               let uu____8858 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____8858 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____8908 =
                        let uu____8909 = FStar_Syntax_Subst.compress head3
                           in
                        uu____8909.FStar_Syntax_Syntax.n  in
                      match uu____8908 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____8912,us) -> us
                      | uu____8918 -> []  in
                    let uu____8919 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____8919 with
                     | (uu____8942,args1) ->
                         let uu____8968 =
                           let uu____8991 = FStar_List.hd args1  in
                           let uu____9008 = FStar_List.tl args1  in
                           (uu____8991, uu____9008)  in
                         (match uu____8968 with
                          | (res,args2) ->
                              let uu____9089 =
                                let uu____9098 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___338_9126  ->
                                          match uu___338_9126 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____9134 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____9134 with
                                               | (env1,uu____9146) ->
                                                   let uu____9151 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____9151 with
                                                    | (e1,uu____9163,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____9098
                                  FStar_List.unzip
                                 in
                              (match uu____9089 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___354_9204 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___354_9204.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___354_9204.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____9210 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____9210 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____9214 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____9214))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____9224 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____9225 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____9235 = aux u3  in FStar_Syntax_Syntax.U_succ uu____9235
        | FStar_Syntax_Syntax.U_max us ->
            let uu____9239 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____9239
        | FStar_Syntax_Syntax.U_name x ->
            let uu____9243 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____9243
            then u2
            else
              (let uu____9245 =
                 let uu____9246 =
                   let uu____9247 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____9247 " not found"  in
                 Prims.strcat "Universe variable " uu____9246  in
               failwith uu____9245)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____9249 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____9249 FStar_Pervasives_Native.snd
         | uu____9258 -> aux u)

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail1 msg t =
            let uu____9287 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____9287 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____9375 bs2 bs_expected1 =
              match uu____9375 with
              | (env2,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____9545)) ->
                             let uu____9550 =
                               let uu____9555 =
                                 let uu____9556 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9556
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9555)
                                in
                             let uu____9557 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9550 uu____9557
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta uu____9558)) ->
                             let uu____9565 =
                               let uu____9570 =
                                 let uu____9571 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9571
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9570)
                                in
                             let uu____9572 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9565 uu____9572
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____9573),FStar_Pervasives_Native.None ) ->
                             let uu____9578 =
                               let uu____9583 =
                                 let uu____9584 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9584
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9583)
                                in
                             let uu____9585 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9578 uu____9585
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta
                            uu____9586),FStar_Pervasives_Native.None ) ->
                             let uu____9593 =
                               let uu____9598 =
                                 let uu____9599 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9599
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9598)
                                in
                             let uu____9600 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9593 uu____9600
                         | uu____9601 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____9611 =
                           let uu____9618 =
                             let uu____9619 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____9619.FStar_Syntax_Syntax.n  in
                           match uu____9618 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9630 ->
                               ((let uu____9632 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____9632
                                 then
                                   let uu____9633 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____9633
                                 else ());
                                (let uu____9635 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____9635 with
                                 | (t,uu____9649,g1_env) ->
                                     let g2_env =
                                       let uu____9652 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____9652
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____9654 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____9654 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____9657 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____9662 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____9657 uu____9662
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____9664 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____9664
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____9665 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____9665)))
                            in
                         match uu____9611 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___355_9691 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___355_9691.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___355_9691.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____9714 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____9714
                                in
                             let uu____9717 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____9717 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____9782 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____9782,
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
                  | uu____9954 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____9963 = tc_binders env1 bs  in
                  match uu____9963 with
                  | (bs1,envbody,g_env,uu____9993) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____10047 =
                    let uu____10048 = FStar_Syntax_Subst.compress t2  in
                    uu____10048.FStar_Syntax_Syntax.n  in
                  match uu____10047 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____10081 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10101 -> failwith "Impossible");
                       (let uu____10110 = tc_binders env1 bs  in
                        match uu____10110 with
                        | (bs1,envbody,g_env,uu____10152) ->
                            let uu____10153 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10153 with
                             | (envbody1,uu____10191) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____10212;
                         FStar_Syntax_Syntax.pos = uu____10213;
                         FStar_Syntax_Syntax.vars = uu____10214;_},uu____10215)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10259 -> failwith "Impossible");
                       (let uu____10268 = tc_binders env1 bs  in
                        match uu____10268 with
                        | (bs1,envbody,g_env,uu____10310) ->
                            let uu____10311 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10311 with
                             | (envbody1,uu____10349) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____10371) ->
                      let uu____10376 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____10376 with
                       | (uu____10437,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____10514 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____10514 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____10659 c_expected2
                               body3 =
                               match uu____10659 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____10773 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____10773,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____10790 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____10790
                                           in
                                        let uu____10791 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____10791,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____10808 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____10808
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
                                               let uu____10872 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____10872 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____10899 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____10899 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____10954 =
                                                           let uu____10981 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____10981,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____10954
                                                           c_expected4 body3))
                                           | uu____11004 ->
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
                             let uu____11032 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____11032 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___356_11095 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___356_11095.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___356_11095.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___356_11095.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___356_11095.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___356_11095.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___356_11095.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___356_11095.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___356_11095.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___356_11095.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___356_11095.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___356_11095.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___356_11095.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___356_11095.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___356_11095.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___356_11095.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___356_11095.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___356_11095.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___356_11095.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___356_11095.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___356_11095.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___356_11095.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___356_11095.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___356_11095.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___356_11095.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___356_11095.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___356_11095.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___356_11095.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___356_11095.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___356_11095.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___356_11095.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___356_11095.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___356_11095.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___356_11095.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___356_11095.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___356_11095.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___356_11095.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___356_11095.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___356_11095.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___356_11095.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___356_11095.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___356_11095.FStar_TypeChecker_Env.nbe)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____11153  ->
                                     fun uu____11154  ->
                                       match (uu____11153, uu____11154) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____11236 =
                                             let uu____11243 =
                                               let uu____11244 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11244
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____11243 t3  in
                                           (match uu____11236 with
                                            | (t4,uu____11266,uu____11267) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____11279 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___357_11282
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___357_11282.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___357_11282.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____11279 ::
                                                        letrec_binders
                                                  | uu____11283 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____11292 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____11292 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____11368 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____11368 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g_env))))
                  | uu____11428 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____11459 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____11459
                      else
                        (let uu____11461 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____11461 with
                         | (uu____11510,bs1,uu____11512,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____11542 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____11542 with
          | (env1,topt) ->
              ((let uu____11562 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____11562
                then
                  let uu____11563 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____11563
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____11567 = expected_function_typ1 env1 topt body  in
                match uu____11567 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____11608 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____11608
                      then
                        let uu____11609 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____11610 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____11609 uu____11610
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____11613 =
                        let should_check_expected_effect =
                          let uu____11625 =
                            let uu____11632 =
                              let uu____11633 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____11633.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____11632)  in
                          match uu____11625 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____11638,(FStar_Util.Inr
                                           expected_c,uu____11640),uu____11641))
                              -> false
                          | uu____11690 -> true  in
                        let uu____11697 =
                          tc_term
                            (let uu___358_11706 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___358_11706.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___358_11706.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___358_11706.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___358_11706.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___358_11706.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___358_11706.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___358_11706.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___358_11706.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___358_11706.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___358_11706.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___358_11706.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___358_11706.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___358_11706.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___358_11706.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___358_11706.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___358_11706.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___358_11706.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___358_11706.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___358_11706.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___358_11706.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___358_11706.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___358_11706.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___358_11706.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___358_11706.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___358_11706.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___358_11706.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___358_11706.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___358_11706.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___358_11706.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___358_11706.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___358_11706.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___358_11706.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___358_11706.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___358_11706.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___358_11706.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___358_11706.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___358_11706.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___358_11706.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___358_11706.FStar_TypeChecker_Env.dep_graph);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___358_11706.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____11697 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____11731 =
                                let uu____11738 =
                                  let uu____11743 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____11743)  in
                                check_expected_effect
                                  (let uu___359_11746 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___359_11746.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___359_11746.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___359_11746.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___359_11746.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___359_11746.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___359_11746.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___359_11746.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___359_11746.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___359_11746.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___359_11746.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___359_11746.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___359_11746.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___359_11746.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___359_11746.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___359_11746.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___359_11746.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___359_11746.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___359_11746.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___359_11746.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___359_11746.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___359_11746.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___359_11746.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___359_11746.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___359_11746.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___359_11746.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___359_11746.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___359_11746.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___359_11746.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___359_11746.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___359_11746.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___359_11746.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___359_11746.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___359_11746.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___359_11746.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___359_11746.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___359_11746.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___359_11746.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___359_11746.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___359_11746.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___359_11746.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___359_11746.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____11738
                                 in
                              (match uu____11731 with
                               | (body3,cbody1,guard) ->
                                   let uu____11760 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____11760))
                            else
                              (let uu____11766 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____11766, guard_body1))
                         in
                      match uu____11613 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____11791 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____11793 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____11793)
                               in
                            if uu____11791
                            then
                              let uu____11794 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____11795 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____11794
                                uu____11795
                            else
                              (let guard =
                                 let uu____11798 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____11798
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
                          let uu____11812 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____11833
                                     -> (e, t1, guard1)
                                 | uu____11848 ->
                                     let uu____11849 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____11849 with
                                      | (e1,guard') ->
                                          let uu____11862 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____11862)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____11812 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____11873 =
                                 let uu____11878 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____11878 guard2
                                  in
                               (match uu____11873 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3)
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
              (let uu____11926 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____11926
               then
                 let uu____11927 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____11928 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____11927
                   uu____11928
               else ());
              (let monadic_application uu____12005 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____12005 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____12072 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____12072 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___360_12086 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___360_12086.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___360_12086.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___360_12086.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____12087 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____12103 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____12103
                                   in
                                (cres1, g)
                            | uu____12104 ->
                                let g =
                                  let uu____12114 =
                                    let uu____12115 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____12115
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____12114
                                   in
                                let uu____12116 =
                                  let uu____12117 =
                                    let uu____12118 =
                                      let uu____12119 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____12119
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____12118
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____12117
                                   in
                                (uu____12116, g)
                             in
                          (match uu____12087 with
                           | (cres2,guard1) ->
                               ((let uu____12131 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____12131
                                 then
                                   let uu____12132 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____12132
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____12148  ->
                                             match uu____12148 with
                                             | (uu____12157,uu____12158,lc)
                                                 ->
                                                 (let uu____12166 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____12166)
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
                                   let uu____12178 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____12178
                                   then
                                     ((let uu____12180 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12180
                                       then
                                         let uu____12181 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____12181
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____12185 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12185
                                       then
                                         let uu____12186 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____12186
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____12214  ->
                                          match uu____12214 with
                                          | ((e,q),x,c) ->
                                              ((let uu____12256 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12256
                                                then
                                                  let uu____12257 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____12259 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12260 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____12257 uu____12259
                                                    uu____12260
                                                else ());
                                               (let uu____12262 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12262
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
                                   (let uu____12270 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____12270
                                    then
                                      let uu____12271 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____12271
                                    else ());
                                   (let uu____12273 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____12273
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
                                   let uu____12281 =
                                     let uu____12282 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____12282.FStar_Syntax_Syntax.n  in
                                   match uu____12281 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____12286 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____12307  ->
                                              match uu____12307 with
                                              | (arg,uu____12321,uu____12322)
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
                                     (let uu____12332 =
                                        let map_fun uu____12394 =
                                          match uu____12394 with
                                          | ((e,q),uu____12431,c) ->
                                              ((let uu____12448 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12448
                                                then
                                                  let uu____12449 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12450 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____12449 uu____12450
                                                else ());
                                               (let uu____12452 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12452
                                                then
                                                  ((let uu____12474 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____12474
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  ((let uu____12504 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____12504
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
                                                    let uu____12508 =
                                                      let uu____12515 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____12515, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____12508)))))
                                           in
                                        let uu____12542 =
                                          let uu____12571 =
                                            let uu____12598 =
                                              let uu____12609 =
                                                let uu____12618 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____12618,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____12609 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____12598
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____12571
                                           in
                                        match uu____12542 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____12807 =
                                              let uu____12808 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____12808
                                               in
                                            let uu____12823 =
                                              let uu____12824 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____12824  in
                                            (lifted_args, uu____12807,
                                              uu____12823)
                                         in
                                      match uu____12332 with
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
                                          let bind_lifted_args e
                                            uu___339_12929 =
                                            match uu___339_12929 with
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
                                                  let uu____12990 =
                                                    let uu____12997 =
                                                      let uu____12998 =
                                                        let uu____13011 =
                                                          let uu____13014 =
                                                            let uu____13015 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____13015]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____13014 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____13011)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____12998
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____12997
                                                     in
                                                  uu____12990
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
                                 let uu____13067 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____13067 with
                                 | (comp3,g) ->
                                     ((let uu____13084 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13084
                                       then
                                         let uu____13085 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____13086 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____13085 uu____13086
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____13164 bs args1 =
                 match uu____13164 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13303))::rest,
                         (uu____13305,FStar_Pervasives_Native.None )::uu____13306)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____13366 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____13366 with
                           | (t1,g_ex) ->
                               let uu____13379 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____13379 with
                                | (varg,uu____13399,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____13427 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____13427)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____13435 =
                                      let uu____13470 =
                                        let uu____13481 =
                                          let uu____13490 =
                                            let uu____13491 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____13491
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____13490)
                                           in
                                        uu____13481 :: outargs  in
                                      (subst2, uu____13470, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____13435 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____13537,FStar_Pervasives_Native.None
                                                                 )::uu____13538)
                          ->
                          let uu____13599 = tc_tactic env tau  in
                          (match uu____13599 with
                           | (tau1,uu____13613,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____13616 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____13616 with
                                | (t1,g_ex) ->
                                    let uu____13629 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                       in
                                    (match uu____13629 with
                                     | (varg,uu____13649,implicits) ->
                                         let mark_meta_implicits tau2 g1 =
                                           let uu___361_13674 = g1  in
                                           let uu____13675 =
                                             FStar_List.map
                                               (fun imp  ->
                                                  let uu___362_13681 = imp
                                                     in
                                                  {
                                                    FStar_TypeChecker_Env.imp_reason
                                                      =
                                                      (uu___362_13681.FStar_TypeChecker_Env.imp_reason);
                                                    FStar_TypeChecker_Env.imp_uvar
                                                      =
                                                      (uu___362_13681.FStar_TypeChecker_Env.imp_uvar);
                                                    FStar_TypeChecker_Env.imp_tm
                                                      =
                                                      (uu___362_13681.FStar_TypeChecker_Env.imp_tm);
                                                    FStar_TypeChecker_Env.imp_range
                                                      =
                                                      (uu___362_13681.FStar_TypeChecker_Env.imp_range);
                                                    FStar_TypeChecker_Env.imp_meta
                                                      =
                                                      (FStar_Pervasives_Native.Some
                                                         (env, tau2))
                                                  })
                                               g1.FStar_TypeChecker_Env.implicits
                                              in
                                           {
                                             FStar_TypeChecker_Env.guard_f =
                                               (uu___361_13674.FStar_TypeChecker_Env.guard_f);
                                             FStar_TypeChecker_Env.deferred =
                                               (uu___361_13674.FStar_TypeChecker_Env.deferred);
                                             FStar_TypeChecker_Env.univ_ineqs
                                               =
                                               (uu___361_13674.FStar_TypeChecker_Env.univ_ineqs);
                                             FStar_TypeChecker_Env.implicits
                                               = uu____13675
                                           }  in
                                         let implicits1 =
                                           mark_meta_implicits tau1 implicits
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____13701 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____13701)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits1
                                            in
                                         let uu____13709 =
                                           let uu____13744 =
                                             let uu____13755 =
                                               let uu____13764 =
                                                 let uu____13765 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____13765
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____13764)
                                                in
                                             uu____13755 :: outargs  in
                                           (subst2, uu____13744, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____13709 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____13881,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____13882)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____13891),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____13892)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____13899),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____13900)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____13913 ->
                                let uu____13922 =
                                  let uu____13927 =
                                    let uu____13928 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____13929 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____13930 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____13931 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____13928 uu____13929 uu____13930
                                      uu____13931
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____13927)
                                   in
                                FStar_Errors.raise_error uu____13922
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___363_13934 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___363_13934.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___363_13934.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____13936 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____13936
                             then
                               let uu____13937 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____13938 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____13939 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____13940 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____13941 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____13937 uu____13938 uu____13939
                                 uu____13940 uu____13941
                             else ());
                            (let uu____13943 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____13943 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___364_13958 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___364_13958.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___364_13958.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___364_13958.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___364_13958.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___364_13958.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___364_13958.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___364_13958.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___364_13958.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___364_13958.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___364_13958.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___364_13958.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___364_13958.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___364_13958.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___364_13958.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___364_13958.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___364_13958.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___364_13958.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___364_13958.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___364_13958.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___364_13958.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___364_13958.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___364_13958.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___364_13958.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___364_13958.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___364_13958.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___364_13958.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___364_13958.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___364_13958.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___364_13958.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___364_13958.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___364_13958.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___364_13958.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___364_13958.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___364_13958.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___364_13958.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___364_13958.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___364_13958.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___364_13958.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___364_13958.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___364_13958.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___364_13958.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____13960 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____13960
                                   then
                                     let uu____13961 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____13962 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____13963 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____13961 uu____13962 uu____13963
                                   else ());
                                  (let uu____13965 = tc_term env2 e  in
                                   match uu____13965 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____13982 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____13982
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____14005 =
                                           let uu____14008 =
                                             let uu____14017 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14017
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____14008
                                            in
                                         (uu____14005, aq)  in
                                       let uu____14026 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____14026
                                       then
                                         let subst2 =
                                           let uu____14034 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____14034 e1
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
                      | (uu____14132,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____14168) ->
                          let uu____14219 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____14219 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____14271 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____14271
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____14302 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____14302 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____14324 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____14324)
                                             in
                                          ((let uu____14326 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____14326
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
                                 | uu____14368 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____14376 =
                                         let uu____14377 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____14377.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14376 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____14380;
                                              FStar_Syntax_Syntax.index =
                                                uu____14381;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____14383)
                                           -> norm_tres tres4
                                       | uu____14390 -> tres3  in
                                     let uu____14391 = norm_tres tres1  in
                                     aux true solve ghead2 uu____14391
                                 | uu____14392 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____14394 ->
                                     let uu____14395 =
                                       let uu____14400 =
                                         let uu____14401 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____14402 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____14409 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____14401 uu____14402
                                           uu____14409
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____14400)
                                        in
                                     let uu____14410 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____14395
                                       uu____14410
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____14438 =
                   let uu____14439 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____14439.FStar_Syntax_Syntax.n  in
                 match uu____14438 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____14448 ->
                     let uu____14461 =
                       FStar_List.fold_right
                         (fun uu____14492  ->
                            fun uu____14493  ->
                              match uu____14493 with
                              | (bs,guard1) ->
                                  let uu____14520 =
                                    let uu____14533 =
                                      let uu____14534 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____14534
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____14533
                                     in
                                  (match uu____14520 with
                                   | (t,uu____14550,g) ->
                                       let uu____14564 =
                                         let uu____14567 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____14567 :: bs  in
                                       let uu____14568 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____14564, uu____14568))) args
                         ([], guard)
                        in
                     (match uu____14461 with
                      | (bs,guard1) ->
                          let uu____14585 =
                            let uu____14592 =
                              let uu____14605 =
                                let uu____14606 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____14606
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____14605
                               in
                            match uu____14592 with
                            | (t,uu____14622,g) ->
                                let uu____14636 = FStar_Options.ml_ish ()  in
                                if uu____14636
                                then
                                  let uu____14643 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____14646 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____14643, uu____14646)
                                else
                                  (let uu____14650 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____14653 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____14650, uu____14653))
                             in
                          (match uu____14585 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____14672 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____14672
                                 then
                                   let uu____14673 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____14674 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____14675 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____14673 uu____14674 uu____14675
                                 else ());
                                (let g =
                                   let uu____14678 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____14678
                                    in
                                 let uu____14679 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____14679))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____14680;
                        FStar_Syntax_Syntax.pos = uu____14681;
                        FStar_Syntax_Syntax.vars = uu____14682;_},uu____14683)
                     ->
                     let uu____14720 =
                       FStar_List.fold_right
                         (fun uu____14751  ->
                            fun uu____14752  ->
                              match uu____14752 with
                              | (bs,guard1) ->
                                  let uu____14779 =
                                    let uu____14792 =
                                      let uu____14793 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____14793
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____14792
                                     in
                                  (match uu____14779 with
                                   | (t,uu____14809,g) ->
                                       let uu____14823 =
                                         let uu____14826 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____14826 :: bs  in
                                       let uu____14827 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____14823, uu____14827))) args
                         ([], guard)
                        in
                     (match uu____14720 with
                      | (bs,guard1) ->
                          let uu____14844 =
                            let uu____14851 =
                              let uu____14864 =
                                let uu____14865 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____14865
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____14864
                               in
                            match uu____14851 with
                            | (t,uu____14881,g) ->
                                let uu____14895 = FStar_Options.ml_ish ()  in
                                if uu____14895
                                then
                                  let uu____14902 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____14905 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____14902, uu____14905)
                                else
                                  (let uu____14909 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____14912 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____14909, uu____14912))
                             in
                          (match uu____14844 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____14931 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____14931
                                 then
                                   let uu____14932 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____14933 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____14934 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____14932 uu____14933 uu____14934
                                 else ());
                                (let g =
                                   let uu____14937 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____14937
                                    in
                                 let uu____14938 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____14938))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____14961 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____14961 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____14983 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____14983)  in
                          tc_args head_info ([], [], [], guard, []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____15025) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____15031,uu____15032) ->
                     check_function_app t guard
                 | uu____15073 ->
                     let uu____15074 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____15074
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3)
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
                  let uu____15156 =
                    FStar_List.fold_left2
                      (fun uu____15223  ->
                         fun uu____15224  ->
                           fun uu____15225  ->
                             match (uu____15223, uu____15224, uu____15225)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____15372 =
                                     let uu____15373 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____15373 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____15372
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____15375 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____15375 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____15403 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____15403 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____15407 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____15407)
                                              &&
                                              (let uu____15409 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____15409))
                                          in
                                       let uu____15410 =
                                         let uu____15421 =
                                           let uu____15432 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____15432]  in
                                         FStar_List.append seen uu____15421
                                          in
                                       let uu____15465 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____15410, uu____15465, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____15156 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____15527 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____15527
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____15529 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____15529 with | (c2,g) -> (e, c2, g)))
              | uu____15545 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.pat ->
          (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.bv Prims.list,
            FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,
            FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple6)
  =
  fun env  ->
    fun allow_implicits  ->
      fun pat_t  ->
        fun p0  ->
          let tc_annot env1 t =
            let uu____15579 = FStar_Syntax_Util.type_u ()  in
            match uu____15579 with
            | (tu,u) ->
                let uu____15590 = tc_check_tot_or_gtot_term env1 t tu  in
                (match uu____15590 with | (t1,uu____15602,g) -> (t1, g))
             in
          let uu____15604 =
            FStar_TypeChecker_PatternUtils.pat_as_exp allow_implicits env p0
              tc_annot
             in
          match uu____15604 with
          | (pat_bvs1,exp,guard_pat_annots,p) ->
              ((let uu____15638 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                if uu____15638
                then
                  ((let uu____15640 = FStar_Syntax_Print.pat_to_string p0  in
                    let uu____15641 = FStar_Syntax_Print.pat_to_string p  in
                    FStar_Util.print2 "Pattern %s elaborated to %s\n"
                      uu____15640 uu____15641);
                   (let uu____15642 =
                      FStar_Syntax_Print.bvs_to_string ", " pat_bvs1  in
                    FStar_Util.print1 "pat_bvs = [%s]\n" uu____15642))
                else ());
               (let pat_env =
                  FStar_List.fold_left FStar_TypeChecker_Env.push_bv env
                    pat_bvs1
                   in
                let uu____15645 =
                  FStar_TypeChecker_Env.clear_expected_typ pat_env  in
                match uu____15645 with
                | (env1,uu____15667) ->
                    let env11 =
                      let uu___365_15673 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___365_15673.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___365_15673.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___365_15673.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___365_15673.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___365_15673.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___365_15673.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___365_15673.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___365_15673.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___365_15673.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___365_15673.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern = true;
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___365_15673.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___365_15673.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___365_15673.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___365_15673.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___365_15673.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___365_15673.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___365_15673.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___365_15673.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___365_15673.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___365_15673.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___365_15673.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___365_15673.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___365_15673.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___365_15673.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___365_15673.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___365_15673.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___365_15673.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___365_15673.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___365_15673.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___365_15673.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___365_15673.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___365_15673.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___365_15673.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___365_15673.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___365_15673.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___365_15673.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___365_15673.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___365_15673.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___365_15673.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___365_15673.FStar_TypeChecker_Env.dep_graph);
                        FStar_TypeChecker_Env.nbe =
                          (uu___365_15673.FStar_TypeChecker_Env.nbe)
                      }  in
                    let expected_pat_t =
                      FStar_TypeChecker_Rel.unrefine env pat_t  in
                    ((let uu____15676 =
                        FStar_TypeChecker_Env.debug env FStar_Options.High
                         in
                      if uu____15676
                      then
                        let uu____15677 =
                          FStar_Syntax_Print.term_to_string exp  in
                        let uu____15678 =
                          FStar_Syntax_Print.term_to_string pat_t  in
                        FStar_Util.print2
                          "Checking pattern expression %s against expected type %s\n"
                          uu____15677 uu____15678
                      else ());
                     (let env12 =
                        FStar_TypeChecker_Env.set_expected_typ env11
                          expected_pat_t
                         in
                      let uu____15681 = tc_tot_or_gtot_term env12 exp  in
                      match uu____15681 with
                      | (exp1,lc,g) ->
                          let g1 =
                            let uu___366_15706 = g  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___366_15706.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___366_15706.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___366_15706.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____15707 =
                            let uu____15708 =
                              FStar_TypeChecker_Rel.teq_nosmt env12
                                lc.FStar_Syntax_Syntax.res_typ expected_pat_t
                               in
                            if uu____15708
                            then
                              let env13 =
                                FStar_TypeChecker_Env.set_range env12
                                  exp1.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15710 =
                                FStar_TypeChecker_Rel.discharge_guard_no_smt
                                  env13 g1
                                 in
                              FStar_All.pipe_right uu____15710
                                (FStar_TypeChecker_Rel.resolve_implicits
                                   env13)
                            else
                              (let uu____15712 =
                                 let uu____15717 =
                                   let uu____15718 =
                                     FStar_Syntax_Print.term_to_string
                                       lc.FStar_Syntax_Syntax.res_typ
                                      in
                                   let uu____15719 =
                                     FStar_Syntax_Print.term_to_string
                                       expected_pat_t
                                      in
                                   FStar_Util.format2
                                     "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                     uu____15718 uu____15719
                                    in
                                 (FStar_Errors.Fatal_MismatchedPatternType,
                                   uu____15717)
                                  in
                               FStar_Errors.raise_error uu____15712
                                 exp1.FStar_Syntax_Syntax.pos)
                             in
                          let norm_exp =
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env12 exp1
                             in
                          let uvs_to_string uvs =
                            let uu____15731 =
                              let uu____15734 = FStar_Util.set_elements uvs
                                 in
                              FStar_All.pipe_right uu____15734
                                (FStar_List.map
                                   (fun u  ->
                                      FStar_Syntax_Print.uvar_to_string
                                        u.FStar_Syntax_Syntax.ctx_uvar_head))
                               in
                            FStar_All.pipe_right uu____15731
                              (FStar_String.concat ", ")
                             in
                          let uvs1 = FStar_Syntax_Free.uvars norm_exp  in
                          let uvs2 = FStar_Syntax_Free.uvars expected_pat_t
                             in
                          ((let uu____15752 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Free")
                               in
                            if uu____15752
                            then
                              ((let uu____15754 =
                                  FStar_Syntax_Print.term_to_string norm_exp
                                   in
                                let uu____15755 = uvs_to_string uvs1  in
                                FStar_Util.print2 ">> free_1(%s) = %s\n"
                                  uu____15754 uu____15755);
                               (let uu____15756 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_pat_t
                                   in
                                let uu____15757 = uvs_to_string uvs2  in
                                FStar_Util.print2 ">> free_2(%s) = %s\n"
                                  uu____15756 uu____15757))
                            else ());
                           (let uu____15760 =
                              let uu____15761 =
                                FStar_Util.set_is_subset_of uvs1 uvs2  in
                              FStar_All.pipe_left Prims.op_Negation
                                uu____15761
                               in
                            if uu____15760
                            then
                              let unresolved =
                                FStar_Util.set_difference uvs1 uvs2  in
                              let uu____15765 =
                                let uu____15770 =
                                  let uu____15771 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env norm_exp
                                     in
                                  let uu____15772 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env expected_pat_t
                                     in
                                  let uu____15773 = uvs_to_string unresolved
                                     in
                                  FStar_Util.format3
                                    "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                    uu____15771 uu____15772 uu____15773
                                   in
                                (FStar_Errors.Fatal_UnresolvedPatternVar,
                                  uu____15770)
                                 in
                              FStar_Errors.raise_error uu____15765
                                p.FStar_Syntax_Syntax.p
                            else ());
                           (let uu____15776 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____15776
                            then
                              let uu____15777 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  env exp1
                                 in
                              FStar_Util.print1
                                "Done checking pattern expression %s\n"
                                uu____15777
                            else ());
                           (let p1 =
                              FStar_TypeChecker_Util.decorate_pattern env p
                                exp1
                               in
                            (p1, pat_bvs1, pat_env, exp1, guard_pat_annots,
                              norm_exp)))))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Ident.lident,
          FStar_Syntax_Syntax.cflags Prims.list,Prims.bool ->
                                                  FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple6)
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____15824 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____15824 with
        | (pattern,when_clause,branch_exp) ->
            let uu____15869 = branch1  in
            (match uu____15869 with
             | (cpat,uu____15910,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____15932 =
                   let uu____15939 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____15939
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____15932 with
                  | (scrutinee_env,uu____15972) ->
                      let uu____15977 = tc_pat env true pat_t pattern  in
                      (match uu____15977 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____16027 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____16057 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____16057
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____16075 =
                                      let uu____16082 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____16082 e  in
                                    match uu____16075 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____16027 with
                            | (when_clause1,g_when) ->
                                let uu____16135 = tc_term pat_env branch_exp
                                   in
                                (match uu____16135 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Env.conj_guard
                                         guard_pat_annots g_branch
                                        in
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch1;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____16190 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_17  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_17) uu____16190
                                          in
                                       let uu____16201 =
                                         let eqs =
                                           let uu____16222 =
                                             let uu____16223 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____16223
                                              in
                                           if uu____16222
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____16236 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____16251 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____16254 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____16257 ->
                                                  let uu____16258 =
                                                    let uu____16261 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____16261 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____16258)
                                            in
                                         let uu____16264 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch1
                                            in
                                         match uu____16264 with
                                         | (c1,g_branch2) ->
                                             let uu____16289 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____16306 when
                                                   let uu____16319 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____16319
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
                                                   let uu____16349 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____16350 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____16349, uu____16350)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____16371 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____16371
                                                      in
                                                   let uu____16372 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____16373 =
                                                     let uu____16374 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____16374 g_when
                                                      in
                                                   (uu____16372, uu____16373)
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
                                                   let uu____16392 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____16392, g_when)
                                                in
                                             (match uu____16289 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return =
                                                    let c_weak1 =
                                                      let uu____16432 =
                                                        should_return &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____16432
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____16434 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____16434, g_branch2))
                                          in
                                       match uu____16201 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                           ->
                                           let branch_guard =
                                             let uu____16481 =
                                               let uu____16482 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____16482
                                                in
                                             if uu____16481
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____16524 =
                                                      let uu____16525 =
                                                        let uu____16526 =
                                                          let uu____16529 =
                                                            let uu____16536 =
                                                              FStar_TypeChecker_Env.typ_of_datacon
                                                                env
                                                                f.FStar_Syntax_Syntax.v
                                                               in
                                                            FStar_TypeChecker_Env.datacons_of_typ
                                                              env uu____16536
                                                             in
                                                          FStar_Pervasives_Native.snd
                                                            uu____16529
                                                           in
                                                        FStar_List.length
                                                          uu____16526
                                                         in
                                                      uu____16525 >
                                                        (Prims.parse_int "1")
                                                       in
                                                    if uu____16524
                                                    then
                                                      let discriminator =
                                                        FStar_Syntax_Util.mk_discriminator
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      let uu____16542 =
                                                        FStar_TypeChecker_Env.try_lookup_lid
                                                          env discriminator
                                                         in
                                                      match uu____16542 with
                                                      | FStar_Pervasives_Native.None
                                                           -> []
                                                      | uu____16563 ->
                                                          let disc =
                                                            FStar_Syntax_Syntax.fvar
                                                              discriminator
                                                              (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                 (Prims.parse_int "1"))
                                                              FStar_Pervasives_Native.None
                                                             in
                                                          let disc1 =
                                                            let uu____16578 =
                                                              let uu____16583
                                                                =
                                                                let uu____16584
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                   in
                                                                [uu____16584]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____16583
                                                               in
                                                            uu____16578
                                                              FStar_Pervasives_Native.None
                                                              scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                             in
                                                          let uu____16611 =
                                                            FStar_Syntax_Util.mk_eq2
                                                              FStar_Syntax_Syntax.U_zero
                                                              FStar_Syntax_Util.t_bool
                                                              disc1
                                                              FStar_Syntax_Util.exp_true_bool
                                                             in
                                                          [uu____16611]
                                                    else []  in
                                                  let fail1 uu____16618 =
                                                    let uu____16619 =
                                                      let uu____16620 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____16621 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____16622 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____16620
                                                        uu____16621
                                                        uu____16622
                                                       in
                                                    failwith uu____16619  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____16635) ->
                                                        head_constructor t1
                                                    | uu____16640 -> fail1 ()
                                                     in
                                                  let pat_exp2 =
                                                    let uu____16644 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16644
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match pat_exp2.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      uu____16649 -> []
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_uvar
                                                           uu____16662;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu____16663;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu____16664;_},uu____16665)
                                                      -> []
                                                  | FStar_Syntax_Syntax.Tm_name
                                                      uu____16702 -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      (FStar_Const.Const_unit
                                                      ) -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      c1 ->
                                                      let uu____16704 =
                                                        let uu____16705 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____16705
                                                          scrutinee_tm1
                                                          pat_exp2
                                                         in
                                                      [uu____16704]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      uu____16706 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____16714 =
                                                        let uu____16715 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16715
                                                         in
                                                      if uu____16714
                                                      then []
                                                      else
                                                        (let uu____16719 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____16719)
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      uu____16722 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____16724 =
                                                        let uu____16725 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16725
                                                         in
                                                      if uu____16724
                                                      then []
                                                      else
                                                        (let uu____16729 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____16729)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,args) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____16759 =
                                                        let uu____16760 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16760
                                                         in
                                                      if uu____16759
                                                      then []
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____16767 =
                                                             FStar_All.pipe_right
                                                               args
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____16803
                                                                     ->
                                                                    match uu____16803
                                                                    with
                                                                    | 
                                                                    (ei,uu____16815)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____16825
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____16825
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____16846
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____16860
                                                                    =
                                                                    let uu____16865
                                                                    =
                                                                    let uu____16866
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____16866
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____16867
                                                                    =
                                                                    let uu____16868
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____16868]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____16865
                                                                    uu____16867
                                                                     in
                                                                    uu____16860
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____16767
                                                             FStar_List.flatten
                                                            in
                                                         let uu____16901 =
                                                           discriminate
                                                             scrutinee_tm1 f
                                                            in
                                                         FStar_List.append
                                                           uu____16901
                                                           sub_term_guards)
                                                  | uu____16904 -> []  in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pat =
                                                  let uu____16920 =
                                                    let uu____16921 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____16921
                                                     in
                                                  if uu____16920
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____16924 =
                                                         build_branch_guard
                                                           scrutinee_tm1 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____16924
                                                        in
                                                     let uu____16933 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____16933 with
                                                     | (k,uu____16939) ->
                                                         let uu____16940 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____16940
                                                          with
                                                          | (t1,uu____16948,uu____16949)
                                                              -> t1))
                                                   in
                                                let branch_guard =
                                                  build_and_check_branch_guard
                                                    scrutinee_tm norm_pat_exp
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
                                               g_when1 g_branch2
                                              in
                                           ((let uu____16961 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____16961
                                             then
                                               let uu____16962 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____16962
                                             else ());
                                            (let uu____16964 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____16981 =
                                               let uu____16982 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____16982 guard
                                                in
                                             (uu____16964, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____16981))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____17025 = check_let_bound_def true env1 lb  in
          (match uu____17025 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____17047 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____17068 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____17068, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____17073 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____17073
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____17075 =
                      let uu____17088 =
                        let uu____17103 =
                          let uu____17112 =
                            let uu____17119 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____17119)
                             in
                          [uu____17112]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____17103
                         in
                      FStar_List.hd uu____17088  in
                    match uu____17075 with
                    | (uu____17154,univs1,e11,c11,gvs) ->
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
                        let uu____17168 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____17168))
                  in
               (match uu____17047 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____17185 =
                      let uu____17194 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____17194
                      then
                        let uu____17203 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____17203 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____17232 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____17232
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____17233 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____17233, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____17247 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____17247
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____17253 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____17253
                            then e2
                            else
                              ((let uu____17258 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____17258
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
                    (match uu____17185 with
                     | (e21,c12) ->
                         let cres =
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
                             (FStar_Syntax_Util.comp_effect_name c12) e11
                             lb.FStar_Syntax_Syntax.lbattrs
                             lb.FStar_Syntax_Syntax.lbpos
                            in
                         let uu____17285 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____17296 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____17285, uu____17296,
                           FStar_TypeChecker_Env.trivial_guard))))
      | uu____17297 -> failwith "Impossible"

and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___367_17328 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___367_17328.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___367_17328.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___367_17328.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___367_17328.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___367_17328.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___367_17328.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___367_17328.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___367_17328.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___367_17328.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___367_17328.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___367_17328.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___367_17328.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___367_17328.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___367_17328.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___367_17328.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___367_17328.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___367_17328.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___367_17328.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___367_17328.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___367_17328.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___367_17328.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___367_17328.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___367_17328.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___367_17328.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___367_17328.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___367_17328.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___367_17328.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___367_17328.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___367_17328.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___367_17328.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___367_17328.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___367_17328.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___367_17328.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___367_17328.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___367_17328.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___367_17328.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___367_17328.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___367_17328.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___367_17328.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___367_17328.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___367_17328.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____17329 =
            let uu____17340 =
              let uu____17341 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____17341 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____17340 lb  in
          (match uu____17329 with
           | (e1,uu____17363,c1,g1,annotated) ->
               ((let uu____17368 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____17372 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____17372)
                    in
                 if uu____17368
                 then
                   let uu____17373 =
                     let uu____17378 =
                       let uu____17379 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____17380 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____17379 uu____17380
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____17378)
                      in
                   FStar_Errors.raise_error uu____17373
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___368_17383 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___368_17383.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___368_17383.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____17384 =
                   let uu____17389 =
                     let uu____17390 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____17390]  in
                   FStar_Syntax_Subst.open_term uu____17389 e2  in
                 match uu____17384 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____17434 = tc_term env_x e21  in
                     (match uu____17434 with
                      | (e22,c2,g2) ->
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c2)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c2.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_Syntax_Syntax.res_typ
                              cres.FStar_Syntax_Syntax.eff_name e11
                              lb.FStar_Syntax_Syntax.lbattrs
                              lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____17459 =
                              let uu____17466 =
                                let uu____17467 =
                                  let uu____17480 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____17480)  in
                                FStar_Syntax_Syntax.Tm_let uu____17467  in
                              FStar_Syntax_Syntax.mk uu____17466  in
                            uu____17459 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____17498 =
                              let uu____17499 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____17500 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____17499
                                c1.FStar_Syntax_Syntax.res_typ uu____17500
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_18  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_18)
                              uu____17498
                             in
                          let g21 =
                            let uu____17502 =
                              let uu____17503 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____17503 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____17502
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____17506 =
                            let uu____17507 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____17507  in
                          if uu____17506
                          then
                            let tt =
                              let uu____17517 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____17517
                                FStar_Option.get
                               in
                            ((let uu____17523 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____17523
                              then
                                let uu____17524 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____17525 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____17524 uu____17525
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____17528 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____17528 with
                             | (t,g_ex) ->
                                 ((let uu____17542 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____17542
                                   then
                                     let uu____17543 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____17544 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____17543 uu____17544
                                   else ());
                                  (let uu____17546 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___369_17548 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___369_17548.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___369_17548.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___369_17548.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____17546))))))))
      | uu____17549 -> failwith "Impossible"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____17581 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____17581 with
           | (lbs1,e21) ->
               let uu____17600 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____17600 with
                | (env0,topt) ->
                    let uu____17619 = build_let_rec_env true env0 lbs1  in
                    (match uu____17619 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____17641 = check_let_recs rec_env lbs2  in
                         (match uu____17641 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____17661 =
                                  let uu____17662 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____17662
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____17661
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____17668 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____17668
                                  (fun _0_19  ->
                                     FStar_Pervasives_Native.Some _0_19)
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
                                     let uu____17717 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____17751 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____17751)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____17717
                                      in
                                   FStar_List.map2
                                     (fun uu____17785  ->
                                        fun lb  ->
                                          match uu____17785 with
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
                                let uu____17833 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____17833
                                 in
                              let uu____17834 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____17834 with
                               | (lbs5,e22) ->
                                   ((let uu____17854 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____17854
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____17855 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____17855, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____17866 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____17898 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____17898 with
           | (lbs1,e21) ->
               let uu____17917 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____17917 with
                | (env0,topt) ->
                    let uu____17936 = build_let_rec_env false env0 lbs1  in
                    (match uu____17936 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____17958 =
                           let uu____17965 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____17965
                             (fun uu____17988  ->
                                match uu____17988 with
                                | (lbs3,g) ->
                                    let uu____18007 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____18007))
                            in
                         (match uu____17958 with
                          | (lbs3,g_lbs) ->
                              let uu____18022 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___370_18045 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___370_18045.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___370_18045.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___371_18047 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___371_18047.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____18022 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____18074 = tc_term env2 e21  in
                                   (match uu____18074 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres
                                           in
                                        let cres2 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres1
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____18093 =
                                            let uu____18094 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____18094 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____18093
                                           in
                                        let cres3 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres2
                                           in
                                        let tres =
                                          norm env2
                                            cres3.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres4 =
                                          let uu___372_18104 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___372_18104.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___372_18104.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___372_18104.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____18112 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____18112))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____18113 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____18113 with
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
                                                  uu____18151 ->
                                                  (e, cres4, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____18152 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____18152 with
                                                   | (tres1,g_ex) ->
                                                       let cres5 =
                                                         let uu___373_18166 =
                                                           cres4  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___373_18166.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___373_18166.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___373_18166.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____18167 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres5,
                                                         uu____18167))))))))))
      | uu____18168 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____18213 = FStar_Options.ml_ish ()  in
          if uu____18213
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____18216 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____18216 with
             | (formals,c) ->
                 let uu____18247 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____18247 with
                  | (actuals,uu____18257,uu____18258) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____18275 =
                          let uu____18280 =
                            let uu____18281 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____18282 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____18281 uu____18282
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____18280)
                           in
                        FStar_Errors.raise_error uu____18275
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____18285 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____18285 actuals
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
                                (let uu____18312 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____18312)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____18332 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____18332)
                               in
                            let msg =
                              let uu____18340 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____18341 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____18340 uu____18341 formals_msg
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
        let uu____18348 =
          FStar_List.fold_left
            (fun uu____18381  ->
               fun lb  ->
                 match uu____18381 with
                 | (lbs1,env1,g_acc) ->
                     let uu____18406 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____18406 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____18426 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____18443 =
                                 let uu____18450 =
                                   let uu____18451 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____18451
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___374_18462 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___374_18462.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___374_18462.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___374_18462.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___374_18462.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___374_18462.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___374_18462.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___374_18462.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___374_18462.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___374_18462.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___374_18462.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___374_18462.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___374_18462.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___374_18462.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___374_18462.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___374_18462.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___374_18462.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___374_18462.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___374_18462.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___374_18462.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___374_18462.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___374_18462.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___374_18462.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___374_18462.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___374_18462.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___374_18462.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___374_18462.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___374_18462.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___374_18462.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___374_18462.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___374_18462.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___374_18462.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___374_18462.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___374_18462.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___374_18462.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___374_18462.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___374_18462.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___374_18462.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___374_18462.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___374_18462.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___374_18462.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___374_18462.FStar_TypeChecker_Env.nbe)
                                    }) t uu____18450
                                  in
                               match uu____18443 with
                               | (t1,uu____18470,g) ->
                                   let uu____18472 =
                                     let uu____18473 =
                                       let uu____18474 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____18474
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____18473
                                      in
                                   let uu____18475 = norm env01 t1  in
                                   (uu____18472, uu____18475))
                             in
                          (match uu____18426 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____18495 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____18495
                                 then
                                   let uu___375_18496 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___375_18496.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___375_18496.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___375_18496.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___375_18496.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___375_18496.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___375_18496.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___375_18496.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___375_18496.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___375_18496.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___375_18496.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___375_18496.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___375_18496.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___375_18496.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___375_18496.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___375_18496.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___375_18496.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___375_18496.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___375_18496.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___375_18496.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___375_18496.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___375_18496.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___375_18496.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___375_18496.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___375_18496.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___375_18496.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___375_18496.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___375_18496.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___375_18496.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___375_18496.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___375_18496.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___375_18496.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___375_18496.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___375_18496.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___375_18496.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___375_18496.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___375_18496.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___375_18496.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___375_18496.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___375_18496.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___375_18496.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___375_18496.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___376_18509 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___376_18509.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___376_18509.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___376_18509.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___376_18509.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____18348 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____18535 =
        let uu____18544 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____18570 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____18570 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____18600 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____18600
                       | uu____18605 ->
                           let lb1 =
                             let uu___377_18608 = lb  in
                             let uu____18609 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____18609;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___377_18608.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____18612 =
                             let uu____18619 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____18619
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____18612 with
                            | (e,c,g) ->
                                ((let uu____18628 =
                                    let uu____18629 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____18629  in
                                  if uu____18628
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
        FStar_All.pipe_right uu____18544 FStar_List.unzip  in
      match uu____18535 with
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t,Prims.bool)
          FStar_Pervasives_Native.tuple5)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____18678 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____18678 with
        | (env1,uu____18696) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____18704 = check_lbtyp top_level env lb  in
            (match uu____18704 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____18748 =
                     tc_maybe_toplevel_term
                       (let uu___378_18757 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___378_18757.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___378_18757.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___378_18757.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___378_18757.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___378_18757.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___378_18757.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___378_18757.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___378_18757.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___378_18757.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___378_18757.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___378_18757.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___378_18757.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___378_18757.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___378_18757.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___378_18757.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___378_18757.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___378_18757.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___378_18757.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___378_18757.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___378_18757.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___378_18757.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___378_18757.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___378_18757.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___378_18757.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___378_18757.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___378_18757.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___378_18757.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___378_18757.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___378_18757.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___378_18757.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___378_18757.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___378_18757.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___378_18757.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___378_18757.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___378_18757.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___378_18757.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___378_18757.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___378_18757.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___378_18757.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___378_18757.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___378_18757.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____18748 with
                   | (e12,c1,g1) ->
                       let uu____18771 =
                         let uu____18776 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____18781  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____18776 e12 c1 wf_annot
                          in
                       (match uu____18771 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____18796 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____18796
                              then
                                let uu____18797 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____18798 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____18799 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____18797 uu____18798 uu____18799
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.subst_elt
                                           Prims.list,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple5)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____18833 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____18833 with
             | (univ_opening,univ_vars1) ->
                 let uu____18866 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____18866))
        | uu____18871 ->
            let uu____18872 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____18872 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____18921 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____18921)
                 else
                   (let uu____18927 = FStar_Syntax_Util.type_u ()  in
                    match uu____18927 with
                    | (k,uu____18947) ->
                        let uu____18948 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____18948 with
                         | (t2,uu____18970,g) ->
                             ((let uu____18973 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____18973
                               then
                                 let uu____18974 =
                                   let uu____18975 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____18975
                                    in
                                 let uu____18976 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____18974 uu____18976
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____18979 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____18979))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                 FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____18985  ->
      match uu____18985 with
      | (x,imp) ->
          let uu____19012 = FStar_Syntax_Util.type_u ()  in
          (match uu____19012 with
           | (tu,u) ->
               ((let uu____19034 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____19034
                 then
                   let uu____19035 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____19036 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____19037 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____19035 uu____19036 uu____19037
                 else ());
                (let uu____19039 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____19039 with
                 | (t,uu____19061,g) ->
                     let x1 =
                       ((let uu___379_19073 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___379_19073.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___379_19073.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____19075 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____19075
                       then
                         let uu____19076 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____19079 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____19076 uu____19079
                       else ());
                      (let uu____19081 = push_binding env x1  in
                       (x1, uu____19081, g, u))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun bs  ->
      (let uu____19093 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____19093
       then
         let uu____19094 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____19094
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____19203 = tc_binder env1 b  in
             (match uu____19203 with
              | (b1,env',g,u) ->
                  let uu____19252 = aux env' bs2  in
                  (match uu____19252 with
                   | (bs3,env'1,g',us) ->
                       let uu____19313 =
                         let uu____19314 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____19314  in
                       ((b1 :: bs3), env'1, uu____19313, (u :: us))))
          in
       aux env bs)

and (tc_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                               FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____19421  ->
             fun uu____19422  ->
               match (uu____19421, uu____19422) with
               | ((t,imp),(args1,g)) ->
                   let uu____19513 = tc_term env1 t  in
                   (match uu____19513 with
                    | (t1,uu____19533,g') ->
                        let uu____19535 =
                          FStar_TypeChecker_Env.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____19535))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____19589  ->
             match uu____19589 with
             | (pats1,g) ->
                 let uu____19616 = tc_args env p  in
                 (match uu____19616 with
                  | (args,g') ->
                      let uu____19629 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____19629))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____19642 = tc_maybe_toplevel_term env e  in
      match uu____19642 with
      | (e1,c,g) ->
          let uu____19658 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____19658
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____19669 =
               let uu____19674 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____19674
               then
                 let uu____19679 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____19679, false)
               else
                 (let uu____19681 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____19681, true))
                in
             match uu____19669 with
             | (target_comp,allow_ghost) ->
                 let uu____19690 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____19690 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____19700 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____19701 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____19700, uu____19701)
                  | uu____19702 ->
                      if allow_ghost
                      then
                        let uu____19711 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____19711
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____19723 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____19723
                           e1.FStar_Syntax_Syntax.pos)))

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t  ->
      let uu____19746 = tc_tot_or_gtot_term env t  in
      match uu____19746 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      (let uu____19778 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____19778
       then
         let uu____19779 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____19779
       else ());
      (let env1 =
         let uu___380_19782 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___380_19782.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___380_19782.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___380_19782.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___380_19782.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___380_19782.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___380_19782.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___380_19782.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___380_19782.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___380_19782.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___380_19782.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___380_19782.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___380_19782.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___380_19782.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___380_19782.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___380_19782.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___380_19782.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___380_19782.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___380_19782.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___380_19782.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___380_19782.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___380_19782.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___380_19782.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___380_19782.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___380_19782.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___380_19782.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___380_19782.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___380_19782.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___380_19782.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___380_19782.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___380_19782.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___380_19782.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___380_19782.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___380_19782.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___380_19782.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___380_19782.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___380_19782.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___380_19782.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___380_19782.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___380_19782.FStar_TypeChecker_Env.dep_graph);
           FStar_TypeChecker_Env.nbe =
             (uu___380_19782.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____19789 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____19824) ->
             let uu____19825 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____19825
          in
       match uu____19789 with
       | (t,c,g) ->
           let uu____19841 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____19841
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____19849 =
                let uu____19854 =
                  let uu____19855 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____19855
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____19854)
                 in
              let uu____19856 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____19849 uu____19856))
  
let level_of_type_fail :
  'Auu____19871 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____19871
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____19887 =
          let uu____19892 =
            let uu____19893 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____19893 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____19892)  in
        let uu____19894 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____19887 uu____19894
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____19929 =
            let uu____19930 = FStar_Syntax_Util.unrefine t1  in
            uu____19930.FStar_Syntax_Syntax.n  in
          match uu____19929 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____19934 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____19937 = FStar_Syntax_Util.type_u ()  in
                 match uu____19937 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___383_19945 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___383_19945.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___383_19945.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___383_19945.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___383_19945.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___383_19945.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___383_19945.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___383_19945.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___383_19945.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___383_19945.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___383_19945.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___383_19945.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___383_19945.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___383_19945.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___383_19945.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___383_19945.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___383_19945.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___383_19945.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___383_19945.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___383_19945.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___383_19945.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___383_19945.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___383_19945.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___383_19945.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___383_19945.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___383_19945.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___383_19945.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___383_19945.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___383_19945.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___383_19945.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___383_19945.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___383_19945.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___383_19945.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___383_19945.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___383_19945.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___383_19945.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___383_19945.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___383_19945.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___383_19945.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___383_19945.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___383_19945.FStar_TypeChecker_Env.dep_graph);
                         FStar_TypeChecker_Env.nbe =
                           (uu___383_19945.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____19949 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____19949
                       | uu____19950 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun e  ->
      let uu____19967 =
        let uu____19968 = FStar_Syntax_Subst.compress e  in
        uu____19968.FStar_Syntax_Syntax.n  in
      match uu____19967 with
      | FStar_Syntax_Syntax.Tm_bvar uu____19973 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____19978 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____20003 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____20019) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____20065) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____20072 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20072 with | ((uu____20083,t),uu____20085) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____20091 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____20091
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20094,(FStar_Util.Inl t,uu____20096),uu____20097) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20144,(FStar_Util.Inr c,uu____20146),uu____20147) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____20195 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____20204;
             FStar_Syntax_Syntax.vars = uu____20205;_},us)
          ->
          let uu____20211 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20211 with
           | ((us',t),uu____20224) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____20230 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____20230)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____20246 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____20247 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____20257) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____20284 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____20284 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____20306  ->
                      match uu____20306 with
                      | (b,uu____20314) ->
                          let uu____20319 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____20319) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____20326 = universe_of_aux env res  in
                 level_of_type env res uu____20326  in
               let u_c =
                 let uu____20330 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____20330 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____20334 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____20334
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
            | FStar_Syntax_Syntax.Tm_bvar uu____20449 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____20466 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____20505 ->
                let uu____20506 = universe_of_aux env hd3  in
                (uu____20506, args1)
            | FStar_Syntax_Syntax.Tm_name uu____20521 ->
                let uu____20522 = universe_of_aux env hd3  in
                (uu____20522, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____20537 ->
                let uu____20550 = universe_of_aux env hd3  in
                (uu____20550, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____20565 ->
                let uu____20572 = universe_of_aux env hd3  in
                (uu____20572, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____20587 ->
                let uu____20614 = universe_of_aux env hd3  in
                (uu____20614, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____20629 ->
                let uu____20636 = universe_of_aux env hd3  in
                (uu____20636, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____20651 ->
                let uu____20652 = universe_of_aux env hd3  in
                (uu____20652, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____20667 ->
                let uu____20682 = universe_of_aux env hd3  in
                (uu____20682, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____20697 ->
                let uu____20704 = universe_of_aux env hd3  in
                (uu____20704, args1)
            | FStar_Syntax_Syntax.Tm_type uu____20719 ->
                let uu____20720 = universe_of_aux env hd3  in
                (uu____20720, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____20735,hd4::uu____20737) ->
                let uu____20802 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____20802 with
                 | (uu____20819,uu____20820,hd5) ->
                     let uu____20838 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____20838 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____20897 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____20899 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____20899 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____20958 ->
                let uu____20959 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____20959 with
                 | (env1,uu____20983) ->
                     let env2 =
                       let uu___384_20989 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___384_20989.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___384_20989.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___384_20989.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___384_20989.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___384_20989.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___384_20989.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___384_20989.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___384_20989.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___384_20989.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___384_20989.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___384_20989.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___384_20989.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___384_20989.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___384_20989.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___384_20989.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___384_20989.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___384_20989.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___384_20989.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___384_20989.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___384_20989.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___384_20989.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___384_20989.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___384_20989.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___384_20989.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___384_20989.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___384_20989.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___384_20989.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___384_20989.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___384_20989.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___384_20989.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___384_20989.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___384_20989.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___384_20989.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___384_20989.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___384_20989.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___384_20989.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___384_20989.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___384_20989.FStar_TypeChecker_Env.dep_graph);
                         FStar_TypeChecker_Env.nbe =
                           (uu___384_20989.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____20991 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____20991
                       then
                         let uu____20992 =
                           let uu____20993 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____20993  in
                         let uu____20994 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____20992 uu____20994
                       else ());
                      (let uu____20996 = tc_term env2 hd3  in
                       match uu____20996 with
                       | (uu____21019,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____21020;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____21022;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____21023;_},g)
                           ->
                           ((let uu____21037 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____21037
                               (fun a236  -> ()));
                            (t, args1)))))
             in
          let uu____21050 = type_of_head true hd1 args  in
          (match uu____21050 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____21096 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____21096 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____21150 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____21150)))
      | FStar_Syntax_Syntax.Tm_match (uu____21153,hd1::uu____21155) ->
          let uu____21220 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____21220 with
           | (uu____21223,uu____21224,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____21242,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____21289 = universe_of_aux env e  in
      level_of_type env e uu____21289
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____21314 = tc_binders env tps  in
      match uu____21314 with
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
      let uu____21368 =
        let uu____21369 = FStar_Syntax_Subst.compress t  in
        uu____21369.FStar_Syntax_Syntax.n  in
      match uu____21368 with
      | FStar_Syntax_Syntax.Tm_delayed uu____21374 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____21399 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____21404 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____21404
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____21406 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21406
            (fun uu____21420  ->
               match uu____21420 with
               | (t1,uu____21428) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____21430;
             FStar_Syntax_Syntax.vars = uu____21431;_},us)
          ->
          let uu____21437 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21437
            (fun uu____21451  ->
               match uu____21451 with
               | (t1,uu____21459) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____21461 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____21461
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____21463 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____21463
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____21468;_})
          ->
          let mk_comp =
            let uu____21512 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____21512
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____21540 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____21540
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____21607 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____21607
                 (fun u  ->
                    let uu____21615 =
                      let uu____21618 =
                        let uu____21625 =
                          let uu____21626 =
                            let uu____21641 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____21641)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____21626  in
                        FStar_Syntax_Syntax.mk uu____21625  in
                      uu____21618 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____21615))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____21681 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____21681 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____21740 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____21740
                       (fun uc  ->
                          let uu____21748 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____21748)
                 | (x,imp)::bs3 ->
                     let uu____21774 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____21774
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____21783 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____21803) ->
          let uu____21808 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____21808
            (fun u_x  ->
               let uu____21816 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____21816)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____21862 =
              let uu____21863 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____21863.FStar_Syntax_Syntax.n  in
            match uu____21862 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____21945 = FStar_Util.first_N n_args bs  in
                    match uu____21945 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____22037 =
                          let uu____22042 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____22042  in
                        (match uu____22037 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____22102 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____22102 with
                       | (bs1,c1) ->
                           let uu____22123 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____22123
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____22201  ->
                     match uu____22201 with
                     | (bs1,t1) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____22277 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____22277)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____22279) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____22285,uu____22286) ->
                aux t1
            | uu____22327 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22328,(FStar_Util.Inl t1,uu____22330),uu____22331) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22378,(FStar_Util.Inr c,uu____22380),uu____22381) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____22446 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____22446
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____22454) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____22459 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____22482 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____22495 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____22506 = type_of_well_typed_term env t  in
      match uu____22506 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____22512;
            FStar_Syntax_Syntax.vars = uu____22513;_}
          -> FStar_Pervasives_Native.Some u
      | uu____22516 -> FStar_Pervasives_Native.None

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
            let uu___385_22541 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___385_22541.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___385_22541.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___385_22541.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___385_22541.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___385_22541.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___385_22541.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___385_22541.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___385_22541.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___385_22541.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___385_22541.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___385_22541.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___385_22541.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___385_22541.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___385_22541.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___385_22541.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___385_22541.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___385_22541.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___385_22541.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___385_22541.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___385_22541.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___385_22541.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___385_22541.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___385_22541.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___385_22541.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___385_22541.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___385_22541.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___385_22541.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___385_22541.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___385_22541.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___385_22541.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___385_22541.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___385_22541.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___385_22541.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___385_22541.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___385_22541.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___385_22541.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___385_22541.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___385_22541.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___385_22541.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___385_22541.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___385_22541.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____22547 =
            if must_total
            then
              let uu____22548 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____22548 with | (uu____22555,uu____22556,g) -> g
            else
              (let uu____22559 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____22559 with | (uu____22566,uu____22567,g) -> g)
             in
          let uu____22569 =
            let uu____22570 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____22570  in
          if uu____22569
          then slow_check ()
          else
            (let uu____22572 = type_of_well_typed_term env2 t  in
             match uu____22572 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____22577 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____22577
                   then
                     let uu____22578 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____22579 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____22580 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____22581 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____22578 uu____22579 uu____22580 uu____22581
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____22585 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____22585
                    then
                      let uu____22586 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____22587 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____22588 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____22589 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____22586 (if b then "succeeded" else "failed")
                        uu____22587 uu____22588 uu____22589
                    else ());
                   if b
                   then FStar_TypeChecker_Env.trivial_guard
                   else slow_check ())))
  