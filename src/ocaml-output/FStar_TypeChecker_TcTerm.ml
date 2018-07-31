open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___343_6 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___343_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___343_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___343_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___343_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___343_6.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___343_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___343_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___343_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___343_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___343_6.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___343_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___343_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___343_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___343_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___343_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___343_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___343_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___343_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___343_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___343_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___343_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___343_6.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___343_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___343_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___343_6.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___343_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___343_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___343_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___343_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___343_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___343_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___343_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___343_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___343_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___343_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___343_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___343_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___343_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___343_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___343_6.FStar_TypeChecker_Env.dep_graph);
      FStar_TypeChecker_Env.nbe = (uu___343_6.FStar_TypeChecker_Env.nbe)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___344_12 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___344_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___344_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___344_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___344_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___344_12.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___344_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___344_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___344_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___344_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___344_12.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___344_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___344_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___344_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___344_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___344_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___344_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___344_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___344_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___344_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___344_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___344_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___344_12.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___344_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___344_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___344_12.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___344_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___344_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___344_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___344_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___344_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___344_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___344_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___344_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___344_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___344_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___344_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___344_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___344_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___344_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___344_12.FStar_TypeChecker_Env.dep_graph);
      FStar_TypeChecker_Env.nbe = (uu___344_12.FStar_TypeChecker_Env.nbe)
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
  fun uu___336_113  ->
    match uu___336_113 with
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
              let uu___345_1452 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___345_1452.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___345_1452.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___345_1452.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___345_1452.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___345_1452.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___345_1452.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___345_1452.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___345_1452.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___345_1452.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___345_1452.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___345_1452.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___345_1452.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___345_1452.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___345_1452.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___345_1452.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___345_1452.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___345_1452.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___345_1452.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___345_1452.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___345_1452.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___345_1452.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___345_1452.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___345_1452.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___345_1452.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___345_1452.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___345_1452.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___345_1452.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___345_1452.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___345_1452.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___345_1452.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___345_1452.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___345_1452.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___345_1452.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___345_1452.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___345_1452.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___345_1452.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___345_1452.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___345_1452.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___345_1452.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___345_1452.FStar_TypeChecker_Env.dep_graph);
                FStar_TypeChecker_Env.nbe =
                  (uu___345_1452.FStar_TypeChecker_Env.nbe)
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
                      (fun uu___337_1625  ->
                         match uu___337_1625 with
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
                                   let uu___346_1950 = last1  in
                                   let uu____1951 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___346_1950.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___346_1950.FStar_Syntax_Syntax.index);
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
               let uu____2055 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2055)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____2653 =
        FStar_Util.record_time
          (fun uu____2671  ->
             tc_maybe_toplevel_term
               (let uu___347_2674 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___347_2674.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___347_2674.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___347_2674.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___347_2674.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___347_2674.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___347_2674.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___347_2674.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___347_2674.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___347_2674.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___347_2674.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___347_2674.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___347_2674.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___347_2674.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___347_2674.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___347_2674.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level = false;
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___347_2674.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___347_2674.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___347_2674.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___347_2674.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___347_2674.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___347_2674.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___347_2674.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___347_2674.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___347_2674.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___347_2674.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___347_2674.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___347_2674.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___347_2674.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___347_2674.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___347_2674.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___347_2674.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___347_2674.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___347_2674.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___347_2674.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___347_2674.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___347_2674.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___347_2674.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___347_2674.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___347_2674.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___347_2674.FStar_TypeChecker_Env.dep_graph);
                  FStar_TypeChecker_Env.nbe =
                    (uu___347_2674.FStar_TypeChecker_Env.nbe)
                }) e)
         in
      match uu____2653 with
      | (r,ms) ->
          ((let uu____2696 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____2696
            then
              ((let uu____2698 =
                  let uu____2699 = FStar_TypeChecker_Env.get_range env  in
                  FStar_All.pipe_left FStar_Range.string_of_range uu____2699
                   in
                let uu____2700 = FStar_Syntax_Print.term_to_string e  in
                let uu____2701 =
                  let uu____2702 = FStar_Syntax_Subst.compress e  in
                  FStar_Syntax_Print.tag_of_term uu____2702  in
                let uu____2703 = FStar_Util.string_of_int ms  in
                FStar_Util.print4 "(%s) tc_term of %s (%s) took %sms\n"
                  uu____2698 uu____2700 uu____2701 uu____2703);
               (let uu____2704 = r  in
                match uu____2704 with
                | (e1,uu____2712,uu____2713) ->
                    let uu____2714 =
                      let uu____2715 = FStar_TypeChecker_Env.get_range env
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____2715
                       in
                    let uu____2716 = FStar_Syntax_Print.term_to_string e1  in
                    let uu____2717 =
                      let uu____2718 = FStar_Syntax_Subst.compress e1  in
                      FStar_Syntax_Print.tag_of_term uu____2718  in
                    FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____2714
                      uu____2716 uu____2717))
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
      (let uu____2732 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2732
       then
         let uu____2733 =
           let uu____2734 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2734  in
         let uu____2735 = FStar_Syntax_Print.tag_of_term top  in
         let uu____2736 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2733 uu____2735
           uu____2736
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2744 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2773 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2780 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2793 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2794 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2795 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2796 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2797 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2816 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2831 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2838 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___338_2854 =
             match uu___338_2854 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____2860 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____2873 =
                 let uu____2874 = FStar_Syntax_Subst.compress t  in
                 uu____2874.FStar_Syntax_Syntax.n  in
               match uu____2873 with
               | FStar_Syntax_Syntax.Tm_name uu____2877 -> true
               | uu____2878 -> false  in
             FStar_Util.for_some
               (fun uu____2887  ->
                  match uu____2887 with
                  | (uu____2892,t) ->
                      let uu____2894 = is_name1 t  in
                      Prims.op_Negation uu____2894)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____2912  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____2955  ->
                       match uu____2955 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___348_2984 = qi  in
                  let uu____2985 =
                    FStar_List.map
                      (fun uu____3013  ->
                         match uu____3013 with
                         | ((bv,uu____3029),bv') ->
                             let uu____3041 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____3041)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___348_2984.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____2985
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
                         let uu____3056 =
                           let uu____3063 =
                             let uu____3064 =
                               let uu____3077 =
                                 let uu____3080 =
                                   let uu____3081 =
                                     let uu____3088 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____3088
                                      in
                                   [uu____3081]  in
                                 FStar_Syntax_Subst.close uu____3080 t  in
                               ((false, [lb]), uu____3077)  in
                             FStar_Syntax_Syntax.Tm_let uu____3064  in
                           FStar_Syntax_Syntax.mk uu____3063  in
                         uu____3056 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____3124 =
                  FStar_List.fold_right
                    (fun uu____3160  ->
                       fun uu____3161  ->
                         match (uu____3160, uu____3161) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____3230 = tc_term env_tm tm  in
                             (match uu____3230 with
                              | (tm1,uu____3248,g) ->
                                  let uu____3250 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____3250))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____3124 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___349_3292 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___349_3292.FStar_Syntax_Syntax.qkind);
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
                let uu____3311 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____3311 with
                 | (env',uu____3325) ->
                     let uu____3330 =
                       tc_term
                         (let uu___350_3339 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___350_3339.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___350_3339.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___350_3339.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___350_3339.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___350_3339.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___350_3339.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___350_3339.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___350_3339.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___350_3339.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___350_3339.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___350_3339.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___350_3339.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___350_3339.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___350_3339.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___350_3339.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___350_3339.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___350_3339.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___350_3339.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___350_3339.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___350_3339.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___350_3339.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___350_3339.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___350_3339.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___350_3339.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___350_3339.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___350_3339.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___350_3339.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___350_3339.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___350_3339.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___350_3339.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___350_3339.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___350_3339.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___350_3339.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___350_3339.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___350_3339.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___350_3339.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___350_3339.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___350_3339.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___350_3339.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___350_3339.FStar_TypeChecker_Env.dep_graph);
                            FStar_TypeChecker_Env.nbe =
                              (uu___350_3339.FStar_TypeChecker_Env.nbe)
                          }) qt
                        in
                     (match uu____3330 with
                      | (qt1,uu____3347,uu____3348) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____3354 =
                            let uu____3361 =
                              let uu____3366 =
                                FStar_Syntax_Util.lcomp_of_comp c  in
                              FStar_Util.Inr uu____3366  in
                            value_check_expected_typ env1 top uu____3361
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____3354 with
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
           { FStar_Syntax_Syntax.blob = uu____3383;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____3384;
             FStar_Syntax_Syntax.ltyp = uu____3385;
             FStar_Syntax_Syntax.rng = uu____3386;_}
           ->
           let uu____3397 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____3397
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____3404 = tc_tot_or_gtot_term env1 e1  in
           (match uu____3404 with
            | (e2,c,g) ->
                let g1 =
                  let uu___351_3421 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___351_3421.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___351_3421.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___351_3421.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____3422 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____3422, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____3443 = FStar_Syntax_Util.type_u ()  in
           (match uu____3443 with
            | (t,u) ->
                let uu____3456 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____3456 with
                 | (e2,c,g) ->
                     let uu____3472 =
                       let uu____3489 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____3489 with
                       | (env2,uu____3513) -> tc_pats env2 pats  in
                     (match uu____3472 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___352_3551 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___352_3551.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___352_3551.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___352_3551.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____3552 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____3555 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____3552, c, uu____3555))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____3561 =
             let uu____3562 = FStar_Syntax_Subst.compress e1  in
             uu____3562.FStar_Syntax_Syntax.n  in
           (match uu____3561 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____3571,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____3573;
                               FStar_Syntax_Syntax.lbtyp = uu____3574;
                               FStar_Syntax_Syntax.lbeff = uu____3575;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____3577;
                               FStar_Syntax_Syntax.lbpos = uu____3578;_}::[]),e2)
                ->
                let uu____3606 =
                  let uu____3613 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____3613 e11  in
                (match uu____3606 with
                 | (e12,c1,g1) ->
                     let uu____3623 = tc_term env1 e2  in
                     (match uu____3623 with
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
                            let uu____3647 =
                              let uu____3654 =
                                let uu____3655 =
                                  let uu____3668 =
                                    let uu____3675 =
                                      let uu____3678 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____3678]  in
                                    (false, uu____3675)  in
                                  (uu____3668, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____3655  in
                              FStar_Syntax_Syntax.mk uu____3654  in
                            uu____3647 FStar_Pervasives_Native.None
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
                          let uu____3700 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____3700)))
            | uu____3701 ->
                let uu____3702 = tc_term env1 e1  in
                (match uu____3702 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____3724) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____3736) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____3755 = tc_term env1 e1  in
           (match uu____3755 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____3779) ->
           let uu____3826 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____3826 with
            | (env0,uu____3840) ->
                let uu____3845 = tc_comp env0 expected_c  in
                (match uu____3845 with
                 | (expected_c1,uu____3859,g) ->
                     let uu____3861 =
                       let uu____3868 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____3868 e1  in
                     (match uu____3861 with
                      | (e2,c',g') ->
                          let uu____3878 =
                            let uu____3885 =
                              let uu____3890 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____3890)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____3885
                             in
                          (match uu____3878 with
                           | (e3,expected_c2,g'') ->
                               let uu____3900 = tc_tactic_opt env0 topt  in
                               (match uu____3900 with
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
                                      let uu____3960 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____3960
                                       in
                                    let uu____3961 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____3961 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____3978 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____3978
                                            in
                                         let uu____3979 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____3979)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____3983) ->
           let uu____4030 = FStar_Syntax_Util.type_u ()  in
           (match uu____4030 with
            | (k,u) ->
                let uu____4043 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____4043 with
                 | (t1,uu____4057,f) ->
                     let uu____4059 = tc_tactic_opt env1 topt  in
                     (match uu____4059 with
                      | (topt1,gtac) ->
                          let uu____4078 =
                            let uu____4085 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____4085 e1  in
                          (match uu____4078 with
                           | (e2,c,g) ->
                               let uu____4095 =
                                 let uu____4100 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____4105  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____4100 e2 c f
                                  in
                               (match uu____4095 with
                                | (c1,f1) ->
                                    let uu____4114 =
                                      let uu____4121 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____4121
                                        c1
                                       in
                                    (match uu____4114 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____4168 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____4168
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____4170 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____4170)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____4171;
              FStar_Syntax_Syntax.vars = uu____4172;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4251 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4251 with
            | (unary_op1,uu____4275) ->
                let head1 =
                  let uu____4303 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4303
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
              FStar_Syntax_Syntax.pos = uu____4351;
              FStar_Syntax_Syntax.vars = uu____4352;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4431 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4431 with
            | (unary_op1,uu____4455) ->
                let head1 =
                  let uu____4483 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4483
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
                (FStar_Const.Const_reflect uu____4531);
              FStar_Syntax_Syntax.pos = uu____4532;
              FStar_Syntax_Syntax.vars = uu____4533;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4612 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4612 with
            | (unary_op1,uu____4636) ->
                let head1 =
                  let uu____4664 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____4664
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
              FStar_Syntax_Syntax.pos = uu____4712;
              FStar_Syntax_Syntax.vars = uu____4713;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4809 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4809 with
            | (unary_op1,uu____4833) ->
                let head1 =
                  let uu____4861 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____4861
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
              FStar_Syntax_Syntax.pos = uu____4917;
              FStar_Syntax_Syntax.vars = uu____4918;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____4956 =
             let uu____4963 =
               let uu____4964 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4964  in
             tc_term uu____4963 e1  in
           (match uu____4956 with
            | (e2,c,g) ->
                let uu____4988 = FStar_Syntax_Util.head_and_args top  in
                (match uu____4988 with
                 | (head1,uu____5012) ->
                     let uu____5037 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____5070 =
                       let uu____5071 =
                         let uu____5072 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____5072  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5071
                        in
                     (uu____5037, uu____5070, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5073;
              FStar_Syntax_Syntax.vars = uu____5074;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____5127 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5127 with
            | (head1,uu____5151) ->
                let env' =
                  let uu____5177 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____5177  in
                let uu____5178 = tc_term env' r  in
                (match uu____5178 with
                 | (er,uu____5192,gr) ->
                     let uu____5194 = tc_term env1 t  in
                     (match uu____5194 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____5211 =
                            let uu____5212 =
                              let uu____5217 =
                                let uu____5218 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____5227 =
                                  let uu____5238 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____5238]  in
                                uu____5218 :: uu____5227  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____5217
                               in
                            uu____5212 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____5211, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5273;
              FStar_Syntax_Syntax.vars = uu____5274;_},uu____5275)
           ->
           let uu____5300 =
             let uu____5305 =
               let uu____5306 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____5306  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____5305)  in
           FStar_Errors.raise_error uu____5300 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5313;
              FStar_Syntax_Syntax.vars = uu____5314;_},uu____5315)
           ->
           let uu____5340 =
             let uu____5345 =
               let uu____5346 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____5346  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____5345)  in
           FStar_Errors.raise_error uu____5340 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____5353;
              FStar_Syntax_Syntax.vars = uu____5354;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____5397 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____5397 with
             | (env0,uu____5411) ->
                 let uu____5416 = tc_term env0 e1  in
                 (match uu____5416 with
                  | (e2,c,g) ->
                      let uu____5432 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____5432 with
                       | (reify_op,uu____5456) ->
                           let u_c =
                             let uu____5482 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____5482 with
                             | (uu____5489,c',uu____5491) ->
                                 let uu____5492 =
                                   let uu____5493 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____5493.FStar_Syntax_Syntax.n  in
                                 (match uu____5492 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____5497 ->
                                      let uu____5498 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____5498 with
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
                                                 let uu____5510 =
                                                   let uu____5511 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____5512 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____5513 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____5511 uu____5512
                                                     uu____5513
                                                    in
                                                 failwith uu____5510);
                                            u)))
                              in
                           let ef =
                             let uu____5515 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_Syntax_Util.comp_effect_name uu____5515
                              in
                           ((let uu____5519 =
                               let uu____5520 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef
                                  in
                               Prims.op_Negation uu____5520  in
                             if uu____5519
                             then
                               let uu____5521 =
                                 let uu____5526 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str
                                    in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____5526)
                                  in
                               FStar_Errors.raise_error uu____5521
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____5529 =
                                 FStar_Syntax_Syntax.lcomp_comp c  in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____5529 u_c
                                in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let c1 =
                               let uu____5566 =
                                 FStar_Syntax_Syntax.mk_Total repr  in
                               FStar_All.pipe_right uu____5566
                                 FStar_Syntax_Util.lcomp_of_comp
                                in
                             let uu____5567 =
                               comp_check_expected_typ env1 e3 c1  in
                             match uu____5567 with
                             | (e4,c2,g') ->
                                 let uu____5583 =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 (e4, c2, uu____5583)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____5585;
              FStar_Syntax_Syntax.vars = uu____5586;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____5630 =
               let uu____5631 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____5631  in
             if uu____5630
             then
               let uu____5632 =
                 let uu____5637 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____5637)  in
               FStar_Errors.raise_error uu____5632 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____5639 = FStar_Syntax_Util.head_and_args top  in
             match uu____5639 with
             | (reflect_op,uu____5663) ->
                 let uu____5688 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____5688 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____5727 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____5727 with
                       | (env_no_ex,topt) ->
                           let uu____5746 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____5766 =
                                 let uu____5773 =
                                   let uu____5774 =
                                     let uu____5791 =
                                       let uu____5802 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____5811 =
                                         let uu____5822 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____5822]  in
                                       uu____5802 :: uu____5811  in
                                     (repr, uu____5791)  in
                                   FStar_Syntax_Syntax.Tm_app uu____5774  in
                                 FStar_Syntax_Syntax.mk uu____5773  in
                               uu____5766 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____5870 =
                               let uu____5877 =
                                 let uu____5878 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____5878
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____5877 t  in
                             match uu____5870 with
                             | (t1,uu____5904,g) ->
                                 let uu____5906 =
                                   let uu____5907 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____5907.FStar_Syntax_Syntax.n  in
                                 (match uu____5906 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____5920,(res,uu____5922)::(wp,uu____5924)::[])
                                      -> (t1, res, wp, g)
                                  | uu____5981 -> failwith "Impossible")
                              in
                           (match uu____5746 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____6006 =
                                  let uu____6013 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____6013 with
                                  | (e2,c,g) ->
                                      ((let uu____6030 =
                                          let uu____6031 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____6031
                                           in
                                        if uu____6030
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____6045 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____6045 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____6055 =
                                                let uu____6064 =
                                                  let uu____6071 =
                                                    let uu____6072 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____6073 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____6072 uu____6073
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____6071,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____6064]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____6055);
                                             (let uu____6086 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____6086)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____6090 =
                                              let uu____6091 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____6091
                                               in
                                            (e2, uu____6090)))
                                   in
                                (match uu____6006 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____6107 =
                                         let uu____6108 =
                                           let uu____6109 =
                                             let uu____6110 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____6110]  in
                                           let uu____6111 =
                                             let uu____6122 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____6122]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____6109;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____6111;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____6108
                                          in
                                       FStar_All.pipe_right uu____6107
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____6182 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____6182 with
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
                                          let uu____6205 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____6205))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6244 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6244 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____6294,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____6295))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6347 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6347 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____6422 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____6631 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____6422 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____6748 =
               let uu____6749 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____6749 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____6748 instantiate_both  in
           ((let uu____6765 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____6765
             then
               let uu____6766 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____6767 = FStar_Syntax_Print.term_to_string top  in
               let uu____6768 =
                 let uu____6769 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____6769
                   (fun uu___339_6775  ->
                      match uu___339_6775 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____6766
                 uu____6767 uu____6768
             else ());
            (let uu____6780 = tc_term (no_inst env2) head1  in
             match uu____6780 with
             | (head2,chead,g_head) ->
                 let uu____6796 =
                   let uu____6803 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____6805 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____6805))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____6803
                   then
                     let uu____6812 =
                       let uu____6819 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____6819
                        in
                     match uu____6812 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____6832 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____6832)
                    in
                 (match uu____6796 with
                  | (e1,c,g) ->
                      let uu____6844 =
                        let uu____6851 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____6851
                        then
                          let uu____6858 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____6858 with
                          | (e2,res_typ,implicits) ->
                              let uu____6874 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____6874, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____6844 with
                       | (e2,c1,implicits) ->
                           ((let uu____6886 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____6886
                             then
                               let uu____6887 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____6887
                             else ());
                            (let uu____6889 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____6889 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____6908 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____6908
                                   then
                                     let uu____6909 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____6910 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____6909 uu____6910
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____6950 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____6950 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____6970 = tc_term env12 e1  in
                (match uu____6970 with
                 | (e11,c1,g1) ->
                     let uu____6986 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____7000 = FStar_Syntax_Util.type_u ()  in
                           (match uu____7000 with
                            | (k,uu____7012) ->
                                let uu____7013 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____7013 with
                                 | (res_t,uu____7033,g) ->
                                     let uu____7047 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____7048 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____7047, res_t, uu____7048)))
                        in
                     (match uu____6986 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____7059 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____7059
                            then
                              let uu____7060 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____7060
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
                            let uu____7181 =
                              let uu____7186 =
                                FStar_List.fold_right
                                  (fun uu____7265  ->
                                     fun uu____7266  ->
                                       match (uu____7265, uu____7266) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____7500 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____7500)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____7186 with
                              | (cases,g) ->
                                  let uu____7598 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____7598, g)
                               in
                            match uu____7181 with
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
                                           (fun uu____7738  ->
                                              match uu____7738 with
                                              | ((pat,wopt,br),uu____7782,eff_label,uu____7784,uu____7785,uu____7786)
                                                  ->
                                                  let uu____7821 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____7821)))
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
                                  let uu____7888 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____7888
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____7893 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____7893  in
                                     let lb =
                                       let uu____7897 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____7897 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____7903 =
                                         let uu____7910 =
                                           let uu____7911 =
                                             let uu____7924 =
                                               let uu____7927 =
                                                 let uu____7928 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____7928]  in
                                               FStar_Syntax_Subst.close
                                                 uu____7927 e_match
                                                in
                                             ((false, [lb]), uu____7924)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____7911
                                            in
                                         FStar_Syntax_Syntax.mk uu____7910
                                          in
                                       uu____7903
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____7961 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____7961
                                  then
                                    let uu____7962 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7963 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____7962 uu____7963
                                  else ());
                                 (let uu____7965 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____7965))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7966;
                FStar_Syntax_Syntax.lbunivs = uu____7967;
                FStar_Syntax_Syntax.lbtyp = uu____7968;
                FStar_Syntax_Syntax.lbeff = uu____7969;
                FStar_Syntax_Syntax.lbdef = uu____7970;
                FStar_Syntax_Syntax.lbattrs = uu____7971;
                FStar_Syntax_Syntax.lbpos = uu____7972;_}::[]),uu____7973)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____7996),uu____7997) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8012;
                FStar_Syntax_Syntax.lbunivs = uu____8013;
                FStar_Syntax_Syntax.lbtyp = uu____8014;
                FStar_Syntax_Syntax.lbeff = uu____8015;
                FStar_Syntax_Syntax.lbdef = uu____8016;
                FStar_Syntax_Syntax.lbattrs = uu____8017;
                FStar_Syntax_Syntax.lbpos = uu____8018;_}::uu____8019),uu____8020)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____8045),uu____8046) ->
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
          let uu____8077 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____8116))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____8156 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____8077 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____8187 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____8187 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____8191 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____8191)
                 in
              let uu____8192 = FStar_TypeChecker_Env.clear_expected_typ env
                 in
              (match uu____8192 with
               | (env',uu____8206) ->
                   let uu____8211 = tc_term env' typ  in
                   (match uu____8211 with
                    | (typ1,uu____8225,g1) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                         (let uu____8228 = tc_tactic env' tau  in
                          match uu____8228 with
                          | (tau1,uu____8242,g2) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env'
                                 g2;
                               (let t =
                                  env.FStar_TypeChecker_Env.synth_hook env'
                                    typ1
                                    (let uu___353_8247 = tau1  in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (uu___353_8247.FStar_Syntax_Syntax.n);
                                       FStar_Syntax_Syntax.pos = rng;
                                       FStar_Syntax_Syntax.vars =
                                         (uu___353_8247.FStar_Syntax_Syntax.vars)
                                     })
                                   in
                                (let uu____8249 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Tac")
                                    in
                                 if uu____8249
                                 then
                                   let uu____8250 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   FStar_Util.print1 "Got %s\n" uu____8250
                                 else ());
                                FStar_TypeChecker_Util.check_uvars
                                  tau1.FStar_Syntax_Syntax.pos t;
                                (let uu____8253 =
                                   let uu____8254 =
                                     FStar_Syntax_Syntax.mk_Total typ1  in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.lcomp_of_comp
                                     uu____8254
                                    in
                                 (t, uu____8253,
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
        let uu___354_8258 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___354_8258.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___354_8258.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___354_8258.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___354_8258.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___354_8258.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___354_8258.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___354_8258.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___354_8258.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___354_8258.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___354_8258.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___354_8258.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___354_8258.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___354_8258.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___354_8258.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___354_8258.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___354_8258.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___354_8258.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___354_8258.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___354_8258.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___354_8258.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___354_8258.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___354_8258.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___354_8258.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___354_8258.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___354_8258.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___354_8258.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___354_8258.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___354_8258.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___354_8258.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___354_8258.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___354_8258.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___354_8258.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___354_8258.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___354_8258.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___354_8258.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___354_8258.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___354_8258.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___354_8258.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___354_8258.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___354_8258.FStar_TypeChecker_Env.dep_graph);
          FStar_TypeChecker_Env.nbe =
            (uu___354_8258.FStar_TypeChecker_Env.nbe)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____8280 = tc_tactic env tactic  in
          (match uu____8280 with
           | (tactic1,uu____8294,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____8346 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____8346 with
        | (e2,t,implicits) ->
            let tc =
              let uu____8367 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____8367
              then FStar_Util.Inl t
              else
                (let uu____8373 =
                   let uu____8374 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____8374
                    in
                 FStar_Util.Inr uu____8373)
               in
            let is_data_ctor uu___340_8382 =
              match uu___340_8382 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____8385) -> true
              | uu____8392 -> false  in
            let uu____8395 =
              (is_data_ctor dc) &&
                (let uu____8397 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____8397)
               in
            if uu____8395
            then
              let uu____8404 =
                let uu____8409 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____8409)  in
              let uu____8410 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____8404 uu____8410
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____8427 =
            let uu____8428 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____8428
             in
          failwith uu____8427
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____8453 =
            let uu____8458 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____8458  in
          value_check_expected_typ env1 e uu____8453
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____8460 =
            let uu____8473 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____8473 with
            | FStar_Pervasives_Native.None  ->
                let uu____8488 = FStar_Syntax_Util.type_u ()  in
                (match uu____8488 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____8460 with
           | (t,uu____8525,g0) ->
               let uu____8539 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____8539 with
                | (e1,uu____8559,g1) ->
                    let uu____8573 =
                      let uu____8574 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____8574
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____8575 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____8573, uu____8575)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____8577 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____8586 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____8586)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____8577 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___355_8599 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___355_8599.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___355_8599.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____8602 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____8602 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____8623 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____8623
                       then FStar_Util.Inl t1
                       else
                         (let uu____8629 =
                            let uu____8630 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____8630
                             in
                          FStar_Util.Inr uu____8629)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8632;
             FStar_Syntax_Syntax.vars = uu____8633;_},uu____8634)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8639 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8639
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8647 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8647
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8655;
             FStar_Syntax_Syntax.vars = uu____8656;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____8665 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8665 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____8688 =
                     let uu____8693 =
                       let uu____8694 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____8695 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____8696 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____8694 uu____8695 uu____8696
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____8693)
                      in
                   let uu____8697 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____8688 uu____8697)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____8713 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8717 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8717 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8719 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8719 with
           | ((us,t),range) ->
               ((let uu____8742 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____8742
                 then
                   let uu____8743 =
                     let uu____8744 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____8744  in
                   let uu____8745 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____8746 = FStar_Range.string_of_range range  in
                   let uu____8747 = FStar_Range.string_of_use_range range  in
                   let uu____8748 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____8743 uu____8745 uu____8746 uu____8747 uu____8748
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8753 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8753 us  in
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
          let uu____8781 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8781 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____8795 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8795 with
                | (env2,uu____8809) ->
                    let uu____8814 = tc_binders env2 bs1  in
                    (match uu____8814 with
                     | (bs2,env3,g,us) ->
                         let uu____8833 = tc_comp env3 c1  in
                         (match uu____8833 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___356_8852 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___356_8852.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___356_8852.FStar_Syntax_Syntax.vars)
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
                                  let uu____8863 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____8863
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
          let uu____8879 =
            let uu____8884 =
              let uu____8885 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8885]  in
            FStar_Syntax_Subst.open_term uu____8884 phi  in
          (match uu____8879 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____8913 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8913 with
                | (env2,uu____8927) ->
                    let uu____8932 =
                      let uu____8947 = FStar_List.hd x1  in
                      tc_binder env2 uu____8947  in
                    (match uu____8932 with
                     | (x2,env3,f1,u) ->
                         ((let uu____8983 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____8983
                           then
                             let uu____8984 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____8985 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____8986 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____8984 uu____8985 uu____8986
                           else ());
                          (let uu____8990 = FStar_Syntax_Util.type_u ()  in
                           match uu____8990 with
                           | (t_phi,uu____9002) ->
                               let uu____9003 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____9003 with
                                | (phi2,uu____9017,f2) ->
                                    let e1 =
                                      let uu___357_9022 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___357_9022.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___357_9022.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____9031 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____9031
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____9059) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____9086 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____9086
            then
              let uu____9087 =
                FStar_Syntax_Print.term_to_string
                  (let uu___358_9090 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___358_9090.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___358_9090.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____9087
            else ());
           (let uu____9104 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____9104 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____9117 ->
          let uu____9118 =
            let uu____9119 = FStar_Syntax_Print.term_to_string top  in
            let uu____9120 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____9119
              uu____9120
             in
          failwith uu____9118

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____9130 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____9131,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____9142,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____9158 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____9163 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____9164 ->
            let uu____9166 =
              let uu____9171 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____9171 FStar_Util.must  in
            FStar_All.pipe_right uu____9166 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____9196 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____9197 =
              let uu____9202 =
                let uu____9203 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9203
                 in
              (FStar_Errors.Fatal_IllTyped, uu____9202)  in
            FStar_Errors.raise_error uu____9197 r
        | FStar_Const.Const_set_range_of  ->
            let uu____9204 =
              let uu____9209 =
                let uu____9210 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9210
                 in
              (FStar_Errors.Fatal_IllTyped, uu____9209)  in
            FStar_Errors.raise_error uu____9204 r
        | FStar_Const.Const_reify  ->
            let uu____9211 =
              let uu____9216 =
                let uu____9217 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9217
                 in
              (FStar_Errors.Fatal_IllTyped, uu____9216)  in
            FStar_Errors.raise_error uu____9211 r
        | FStar_Const.Const_reflect uu____9218 ->
            let uu____9219 =
              let uu____9224 =
                let uu____9225 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____9225
                 in
              (FStar_Errors.Fatal_IllTyped, uu____9224)  in
            FStar_Errors.raise_error uu____9219 r
        | uu____9226 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____9243) ->
          let uu____9252 = FStar_Syntax_Util.type_u ()  in
          (match uu____9252 with
           | (k,u) ->
               let uu____9265 = tc_check_tot_or_gtot_term env t k  in
               (match uu____9265 with
                | (t1,uu____9279,g) ->
                    let uu____9281 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____9281, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____9283) ->
          let uu____9292 = FStar_Syntax_Util.type_u ()  in
          (match uu____9292 with
           | (k,u) ->
               let uu____9305 = tc_check_tot_or_gtot_term env t k  in
               (match uu____9305 with
                | (t1,uu____9319,g) ->
                    let uu____9321 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____9321, u, g)))
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
            let uu____9331 =
              let uu____9336 =
                let uu____9337 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____9337 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____9336  in
            uu____9331 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____9356 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____9356 with
           | (tc1,uu____9370,f) ->
               let uu____9372 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____9372 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____9422 =
                        let uu____9423 = FStar_Syntax_Subst.compress head3
                           in
                        uu____9423.FStar_Syntax_Syntax.n  in
                      match uu____9422 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____9426,us) -> us
                      | uu____9432 -> []  in
                    let uu____9433 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____9433 with
                     | (uu____9456,args1) ->
                         let uu____9482 =
                           let uu____9505 = FStar_List.hd args1  in
                           let uu____9522 = FStar_List.tl args1  in
                           (uu____9505, uu____9522)  in
                         (match uu____9482 with
                          | (res,args2) ->
                              let uu____9603 =
                                let uu____9612 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___341_9640  ->
                                          match uu___341_9640 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____9648 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____9648 with
                                               | (env1,uu____9660) ->
                                                   let uu____9665 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____9665 with
                                                    | (e1,uu____9677,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____9612
                                  FStar_List.unzip
                                 in
                              (match uu____9603 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___359_9718 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___359_9718.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___359_9718.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____9724 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____9724 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____9728 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____9728))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____9738 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____9739 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____9749 = aux u3  in FStar_Syntax_Syntax.U_succ uu____9749
        | FStar_Syntax_Syntax.U_max us ->
            let uu____9753 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____9753
        | FStar_Syntax_Syntax.U_name x ->
            let uu____9757 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____9757
            then u2
            else
              (let uu____9759 =
                 let uu____9760 =
                   let uu____9761 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____9761 " not found"  in
                 Prims.strcat "Universe variable " uu____9760  in
               failwith uu____9759)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____9763 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____9763 FStar_Pervasives_Native.snd
         | uu____9772 -> aux u)

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
            let uu____9801 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____9801 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____9889 bs2 bs_expected1 =
              match uu____9889 with
              | (env2,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____10059)) ->
                             let uu____10064 =
                               let uu____10069 =
                                 let uu____10070 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10070
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10069)
                                in
                             let uu____10071 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____10064 uu____10071
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta uu____10072)) ->
                             let uu____10079 =
                               let uu____10084 =
                                 let uu____10085 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10085
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10084)
                                in
                             let uu____10086 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____10079 uu____10086
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____10087),FStar_Pervasives_Native.None ) ->
                             let uu____10092 =
                               let uu____10097 =
                                 let uu____10098 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10098
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10097)
                                in
                             let uu____10099 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____10092 uu____10099
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Meta
                            uu____10100),FStar_Pervasives_Native.None ) ->
                             let uu____10107 =
                               let uu____10112 =
                                 let uu____10113 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____10113
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____10112)
                                in
                             let uu____10114 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____10107 uu____10114
                         | uu____10115 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____10125 =
                           let uu____10132 =
                             let uu____10133 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____10133.FStar_Syntax_Syntax.n  in
                           match uu____10132 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10144 ->
                               ((let uu____10146 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____10146
                                 then
                                   let uu____10147 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____10147
                                 else ());
                                (let uu____10149 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____10149 with
                                 | (t,uu____10163,g1_env) ->
                                     let g2_env =
                                       let uu____10166 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____10166
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____10168 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____10168 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____10171 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____10176 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____10171 uu____10176
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____10178 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____10178
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____10179 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____10179)))
                            in
                         match uu____10125 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___360_10205 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___360_10205.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___360_10205.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____10228 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____10228
                                in
                             let uu____10231 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____10231 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____10296 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____10296,
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
                  | uu____10468 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____10477 = tc_binders env1 bs  in
                  match uu____10477 with
                  | (bs1,envbody,g_env,uu____10507) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____10561 =
                    let uu____10562 = FStar_Syntax_Subst.compress t2  in
                    uu____10562.FStar_Syntax_Syntax.n  in
                  match uu____10561 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____10595 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10615 -> failwith "Impossible");
                       (let uu____10624 = tc_binders env1 bs  in
                        match uu____10624 with
                        | (bs1,envbody,g_env,uu____10666) ->
                            let uu____10667 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10667 with
                             | (envbody1,uu____10705) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____10726;
                         FStar_Syntax_Syntax.pos = uu____10727;
                         FStar_Syntax_Syntax.vars = uu____10728;_},uu____10729)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10773 -> failwith "Impossible");
                       (let uu____10782 = tc_binders env1 bs  in
                        match uu____10782 with
                        | (bs1,envbody,g_env,uu____10824) ->
                            let uu____10825 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10825 with
                             | (envbody1,uu____10863) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____10885) ->
                      let uu____10890 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____10890 with
                       | (uu____10951,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____11028 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____11028 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____11173 c_expected2
                               body3 =
                               match uu____11173 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____11287 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____11287,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____11304 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____11304
                                           in
                                        let uu____11305 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____11305,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____11322 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____11322
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
                                               let uu____11386 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____11386 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____11413 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____11413 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____11468 =
                                                           let uu____11495 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____11495,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____11468
                                                           c_expected4 body3))
                                           | uu____11518 ->
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
                             let uu____11546 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____11546 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___361_11609 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___361_11609.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___361_11609.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___361_11609.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___361_11609.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___361_11609.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___361_11609.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___361_11609.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___361_11609.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___361_11609.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___361_11609.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___361_11609.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___361_11609.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___361_11609.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___361_11609.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___361_11609.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___361_11609.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___361_11609.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___361_11609.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___361_11609.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___361_11609.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___361_11609.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___361_11609.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___361_11609.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___361_11609.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___361_11609.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___361_11609.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___361_11609.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___361_11609.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___361_11609.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___361_11609.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___361_11609.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___361_11609.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___361_11609.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___361_11609.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___361_11609.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___361_11609.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___361_11609.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___361_11609.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___361_11609.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___361_11609.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___361_11609.FStar_TypeChecker_Env.nbe)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____11667  ->
                                     fun uu____11668  ->
                                       match (uu____11667, uu____11668) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____11750 =
                                             let uu____11757 =
                                               let uu____11758 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11758
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____11757 t3  in
                                           (match uu____11750 with
                                            | (t4,uu____11780,uu____11781) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____11793 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___362_11796
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___362_11796.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___362_11796.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____11793 ::
                                                        letrec_binders
                                                  | uu____11797 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____11806 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____11806 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____11882 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____11882 with
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
                  | uu____11942 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____11973 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____11973
                      else
                        (let uu____11975 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____11975 with
                         | (uu____12024,bs1,uu____12026,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____12056 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____12056 with
          | (env1,topt) ->
              ((let uu____12076 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____12076
                then
                  let uu____12077 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____12077
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____12081 = expected_function_typ1 env1 topt body  in
                match uu____12081 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____12122 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____12122
                      then
                        let uu____12123 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____12124 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____12123 uu____12124
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____12127 =
                        let should_check_expected_effect =
                          let uu____12139 =
                            let uu____12146 =
                              let uu____12147 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____12147.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____12146)  in
                          match uu____12139 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____12152,(FStar_Util.Inr
                                           expected_c,uu____12154),uu____12155))
                              -> false
                          | uu____12204 -> true  in
                        let uu____12211 =
                          tc_term
                            (let uu___363_12220 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___363_12220.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___363_12220.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___363_12220.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___363_12220.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___363_12220.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___363_12220.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___363_12220.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___363_12220.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___363_12220.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___363_12220.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___363_12220.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___363_12220.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___363_12220.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___363_12220.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___363_12220.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___363_12220.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___363_12220.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___363_12220.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___363_12220.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___363_12220.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___363_12220.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___363_12220.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___363_12220.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___363_12220.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___363_12220.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___363_12220.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___363_12220.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___363_12220.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___363_12220.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___363_12220.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___363_12220.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___363_12220.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___363_12220.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___363_12220.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___363_12220.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___363_12220.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___363_12220.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___363_12220.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___363_12220.FStar_TypeChecker_Env.dep_graph);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___363_12220.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____12211 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____12245 =
                                let uu____12252 =
                                  let uu____12257 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____12257)  in
                                check_expected_effect
                                  (let uu___364_12260 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___364_12260.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___364_12260.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___364_12260.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___364_12260.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___364_12260.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___364_12260.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___364_12260.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___364_12260.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___364_12260.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___364_12260.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___364_12260.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___364_12260.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___364_12260.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___364_12260.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___364_12260.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___364_12260.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___364_12260.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___364_12260.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___364_12260.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___364_12260.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___364_12260.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___364_12260.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___364_12260.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___364_12260.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___364_12260.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___364_12260.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___364_12260.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___364_12260.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___364_12260.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___364_12260.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___364_12260.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___364_12260.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___364_12260.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___364_12260.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___364_12260.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___364_12260.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___364_12260.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___364_12260.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___364_12260.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___364_12260.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___364_12260.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____12252
                                 in
                              (match uu____12245 with
                               | (body3,cbody1,guard) ->
                                   let uu____12274 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____12274))
                            else
                              (let uu____12280 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____12280, guard_body1))
                         in
                      match uu____12127 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____12305 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____12307 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____12307)
                               in
                            if uu____12305
                            then
                              let uu____12308 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____12309 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____12308
                                uu____12309
                            else
                              (let guard =
                                 let uu____12312 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____12312
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
                          let uu____12326 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____12347
                                     -> (e, t1, guard1)
                                 | uu____12362 ->
                                     let uu____12363 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____12363 with
                                      | (e1,guard') ->
                                          let uu____12376 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____12376)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____12326 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____12387 =
                                 let uu____12392 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____12392 guard2
                                  in
                               (match uu____12387 with
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
              (let uu____12440 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____12440
               then
                 let uu____12441 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____12442 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____12441
                   uu____12442
               else ());
              (let monadic_application uu____12519 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____12519 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____12586 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____12586 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___365_12600 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___365_12600.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___365_12600.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___365_12600.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____12601 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____12617 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____12617
                                   in
                                (cres1, g)
                            | uu____12618 ->
                                let g =
                                  let uu____12628 =
                                    let uu____12629 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____12629
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____12628
                                   in
                                let uu____12630 =
                                  let uu____12631 =
                                    let uu____12632 =
                                      let uu____12633 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____12633
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____12632
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____12631
                                   in
                                (uu____12630, g)
                             in
                          (match uu____12601 with
                           | (cres2,guard1) ->
                               ((let uu____12645 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____12645
                                 then
                                   let uu____12646 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____12646
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____12662  ->
                                             match uu____12662 with
                                             | (uu____12671,uu____12672,lc)
                                                 ->
                                                 (let uu____12680 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____12680)
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
                                   let uu____12692 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____12692
                                   then
                                     ((let uu____12694 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12694
                                       then
                                         let uu____12695 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____12695
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____12699 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12699
                                       then
                                         let uu____12700 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____12700
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____12728  ->
                                          match uu____12728 with
                                          | ((e,q),x,c) ->
                                              ((let uu____12770 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12770
                                                then
                                                  let uu____12771 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____12773 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12774 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____12771 uu____12773
                                                    uu____12774
                                                else ());
                                               (let uu____12776 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12776
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
                                   (let uu____12784 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____12784
                                    then
                                      let uu____12785 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____12785
                                    else ());
                                   (let uu____12787 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____12787
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
                                   let uu____12795 =
                                     let uu____12796 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____12796.FStar_Syntax_Syntax.n  in
                                   match uu____12795 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____12800 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____12821  ->
                                              match uu____12821 with
                                              | (arg,uu____12835,uu____12836)
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
                                     (let uu____12846 =
                                        let map_fun uu____12908 =
                                          match uu____12908 with
                                          | ((e,q),uu____12945,c) ->
                                              ((let uu____12962 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12962
                                                then
                                                  let uu____12963 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12964 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____12963 uu____12964
                                                else ());
                                               (let uu____12966 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12966
                                                then
                                                  ((let uu____12988 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____12988
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  ((let uu____13018 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____13018
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
                                                    let uu____13022 =
                                                      let uu____13029 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____13029, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____13022)))))
                                           in
                                        let uu____13056 =
                                          let uu____13085 =
                                            let uu____13112 =
                                              let uu____13123 =
                                                let uu____13132 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____13132,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____13123 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____13112
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____13085
                                           in
                                        match uu____13056 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____13321 =
                                              let uu____13322 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____13322
                                               in
                                            let uu____13337 =
                                              let uu____13338 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____13338  in
                                            (lifted_args, uu____13321,
                                              uu____13337)
                                         in
                                      match uu____12846 with
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
                                            uu___342_13443 =
                                            match uu___342_13443 with
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
                                                  let uu____13504 =
                                                    let uu____13511 =
                                                      let uu____13512 =
                                                        let uu____13525 =
                                                          let uu____13528 =
                                                            let uu____13529 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____13529]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____13528 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____13525)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____13512
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____13511
                                                     in
                                                  uu____13504
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
                                 let uu____13581 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____13581 with
                                 | (comp3,g) ->
                                     ((let uu____13598 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13598
                                       then
                                         let uu____13599 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____13600 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____13599 uu____13600
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____13678 bs args1 =
                 match uu____13678 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13817))::rest,
                         (uu____13819,FStar_Pervasives_Native.None )::uu____13820)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____13880 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____13880 with
                           | (t1,g_ex) ->
                               let uu____13893 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____13893 with
                                | (varg,uu____13913,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____13941 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____13941)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____13949 =
                                      let uu____13984 =
                                        let uu____13995 =
                                          let uu____14004 =
                                            let uu____14005 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____14005
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____14004)
                                           in
                                        uu____13995 :: outargs  in
                                      (subst2, uu____13984, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____13949 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____14051,FStar_Pervasives_Native.None
                                                                 )::uu____14052)
                          ->
                          let uu____14113 = tc_tactic env tau  in
                          (match uu____14113 with
                           | (tau1,uu____14127,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____14130 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____14130 with
                                | (t1,g_ex) ->
                                    let uu____14143 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                       in
                                    (match uu____14143 with
                                     | (varg,uu____14163,implicits) ->
                                         let mark_meta_implicits tau2 g1 =
                                           let uu___366_14188 = g1  in
                                           let uu____14189 =
                                             FStar_List.map
                                               (fun imp  ->
                                                  let uu___367_14195 = imp
                                                     in
                                                  {
                                                    FStar_TypeChecker_Env.imp_reason
                                                      =
                                                      (uu___367_14195.FStar_TypeChecker_Env.imp_reason);
                                                    FStar_TypeChecker_Env.imp_uvar
                                                      =
                                                      (uu___367_14195.FStar_TypeChecker_Env.imp_uvar);
                                                    FStar_TypeChecker_Env.imp_tm
                                                      =
                                                      (uu___367_14195.FStar_TypeChecker_Env.imp_tm);
                                                    FStar_TypeChecker_Env.imp_range
                                                      =
                                                      (uu___367_14195.FStar_TypeChecker_Env.imp_range);
                                                    FStar_TypeChecker_Env.imp_meta
                                                      =
                                                      (FStar_Pervasives_Native.Some
                                                         (env, tau2))
                                                  })
                                               g1.FStar_TypeChecker_Env.implicits
                                              in
                                           {
                                             FStar_TypeChecker_Env.guard_f =
                                               (uu___366_14188.FStar_TypeChecker_Env.guard_f);
                                             FStar_TypeChecker_Env.deferred =
                                               (uu___366_14188.FStar_TypeChecker_Env.deferred);
                                             FStar_TypeChecker_Env.univ_ineqs
                                               =
                                               (uu___366_14188.FStar_TypeChecker_Env.univ_ineqs);
                                             FStar_TypeChecker_Env.implicits
                                               = uu____14189
                                           }  in
                                         let implicits1 =
                                           mark_meta_implicits tau1 implicits
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____14215 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____14215)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits1
                                            in
                                         let uu____14223 =
                                           let uu____14258 =
                                             let uu____14269 =
                                               let uu____14278 =
                                                 let uu____14279 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____14279
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____14278)
                                                in
                                             uu____14269 :: outargs  in
                                           (subst2, uu____14258, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____14223 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____14395,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____14396)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____14405),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14406)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____14413),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14414)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____14427 ->
                                let uu____14436 =
                                  let uu____14441 =
                                    let uu____14442 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____14443 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____14444 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____14445 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____14442 uu____14443 uu____14444
                                      uu____14445
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____14441)
                                   in
                                FStar_Errors.raise_error uu____14436
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___368_14448 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___368_14448.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___368_14448.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____14450 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____14450
                             then
                               let uu____14451 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____14452 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____14453 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14454 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____14455 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____14451 uu____14452 uu____14453
                                 uu____14454 uu____14455
                             else ());
                            (let uu____14457 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____14457 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___369_14472 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___369_14472.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___369_14472.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___369_14472.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___369_14472.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___369_14472.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___369_14472.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___369_14472.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___369_14472.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___369_14472.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___369_14472.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___369_14472.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___369_14472.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___369_14472.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___369_14472.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___369_14472.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___369_14472.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___369_14472.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___369_14472.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___369_14472.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___369_14472.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___369_14472.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___369_14472.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___369_14472.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___369_14472.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___369_14472.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___369_14472.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___369_14472.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___369_14472.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___369_14472.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___369_14472.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___369_14472.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___369_14472.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___369_14472.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___369_14472.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___369_14472.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___369_14472.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___369_14472.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___369_14472.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___369_14472.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___369_14472.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___369_14472.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____14474 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____14474
                                   then
                                     let uu____14475 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____14476 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____14477 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____14475 uu____14476 uu____14477
                                   else ());
                                  (let uu____14479 = tc_term env2 e  in
                                   match uu____14479 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____14496 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____14496
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____14519 =
                                           let uu____14522 =
                                             let uu____14531 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14531
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____14522
                                            in
                                         (uu____14519, aq)  in
                                       let uu____14540 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____14540
                                       then
                                         let subst2 =
                                           let uu____14548 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____14548 e1
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
                      | (uu____14646,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____14682) ->
                          let uu____14733 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____14733 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____14785 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____14785
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____14816 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____14816 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____14838 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____14838)
                                             in
                                          ((let uu____14840 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____14840
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
                                 | uu____14882 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____14890 =
                                         let uu____14891 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____14891.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14890 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____14894;
                                              FStar_Syntax_Syntax.index =
                                                uu____14895;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____14897)
                                           -> norm_tres tres4
                                       | uu____14904 -> tres3  in
                                     let uu____14905 = norm_tres tres1  in
                                     aux true solve ghead2 uu____14905
                                 | uu____14906 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____14908 ->
                                     let uu____14909 =
                                       let uu____14914 =
                                         let uu____14915 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____14916 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____14923 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____14915 uu____14916
                                           uu____14923
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____14914)
                                        in
                                     let uu____14924 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____14909
                                       uu____14924
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____14952 =
                   let uu____14953 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____14953.FStar_Syntax_Syntax.n  in
                 match uu____14952 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____14962 ->
                     let uu____14975 =
                       FStar_List.fold_right
                         (fun uu____15006  ->
                            fun uu____15007  ->
                              match uu____15007 with
                              | (bs,guard1) ->
                                  let uu____15034 =
                                    let uu____15047 =
                                      let uu____15048 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____15048
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____15047
                                     in
                                  (match uu____15034 with
                                   | (t,uu____15064,g) ->
                                       let uu____15078 =
                                         let uu____15081 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____15081 :: bs  in
                                       let uu____15082 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____15078, uu____15082))) args
                         ([], guard)
                        in
                     (match uu____14975 with
                      | (bs,guard1) ->
                          let uu____15099 =
                            let uu____15106 =
                              let uu____15119 =
                                let uu____15120 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____15120
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____15119
                               in
                            match uu____15106 with
                            | (t,uu____15136,g) ->
                                let uu____15150 = FStar_Options.ml_ish ()  in
                                if uu____15150
                                then
                                  let uu____15157 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____15160 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____15157, uu____15160)
                                else
                                  (let uu____15164 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____15167 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____15164, uu____15167))
                             in
                          (match uu____15099 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____15186 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____15186
                                 then
                                   let uu____15187 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____15188 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____15189 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____15187 uu____15188 uu____15189
                                 else ());
                                (let g =
                                   let uu____15192 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____15192
                                    in
                                 let uu____15193 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____15193))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____15194;
                        FStar_Syntax_Syntax.pos = uu____15195;
                        FStar_Syntax_Syntax.vars = uu____15196;_},uu____15197)
                     ->
                     let uu____15234 =
                       FStar_List.fold_right
                         (fun uu____15265  ->
                            fun uu____15266  ->
                              match uu____15266 with
                              | (bs,guard1) ->
                                  let uu____15293 =
                                    let uu____15306 =
                                      let uu____15307 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____15307
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____15306
                                     in
                                  (match uu____15293 with
                                   | (t,uu____15323,g) ->
                                       let uu____15337 =
                                         let uu____15340 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____15340 :: bs  in
                                       let uu____15341 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____15337, uu____15341))) args
                         ([], guard)
                        in
                     (match uu____15234 with
                      | (bs,guard1) ->
                          let uu____15358 =
                            let uu____15365 =
                              let uu____15378 =
                                let uu____15379 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____15379
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____15378
                               in
                            match uu____15365 with
                            | (t,uu____15395,g) ->
                                let uu____15409 = FStar_Options.ml_ish ()  in
                                if uu____15409
                                then
                                  let uu____15416 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____15419 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____15416, uu____15419)
                                else
                                  (let uu____15423 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____15426 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____15423, uu____15426))
                             in
                          (match uu____15358 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____15445 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____15445
                                 then
                                   let uu____15446 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____15447 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____15448 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____15446 uu____15447 uu____15448
                                 else ());
                                (let g =
                                   let uu____15451 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____15451
                                    in
                                 let uu____15452 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____15452))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____15475 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____15475 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____15497 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____15497)  in
                          tc_args head_info ([], [], [], guard, []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____15539) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____15545,uu____15546) ->
                     check_function_app t guard
                 | uu____15587 ->
                     let uu____15588 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____15588
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
                  let uu____15670 =
                    FStar_List.fold_left2
                      (fun uu____15737  ->
                         fun uu____15738  ->
                           fun uu____15739  ->
                             match (uu____15737, uu____15738, uu____15739)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____15886 =
                                     let uu____15887 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____15887 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____15886
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____15889 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____15889 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____15917 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____15917 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____15921 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____15921)
                                              &&
                                              (let uu____15923 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____15923))
                                          in
                                       let uu____15924 =
                                         let uu____15935 =
                                           let uu____15946 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____15946]  in
                                         FStar_List.append seen uu____15935
                                          in
                                       let uu____15979 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____15924, uu____15979, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____15670 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____16041 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____16041
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____16043 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____16043 with | (c2,g) -> (e, c2, g)))
              | uu____16059 ->
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
            let uu____16093 = FStar_Syntax_Util.type_u ()  in
            match uu____16093 with
            | (tu,u) ->
                let uu____16104 = tc_check_tot_or_gtot_term env1 t tu  in
                (match uu____16104 with | (t1,uu____16116,g) -> (t1, g))
             in
          let uu____16118 =
            FStar_TypeChecker_PatternUtils.pat_as_exp allow_implicits env p0
              tc_annot
             in
          match uu____16118 with
          | (pat_bvs1,exp,guard_pat_annots,p) ->
              ((let uu____16152 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                if uu____16152
                then
                  ((let uu____16154 = FStar_Syntax_Print.pat_to_string p0  in
                    let uu____16155 = FStar_Syntax_Print.pat_to_string p  in
                    FStar_Util.print2 "Pattern %s elaborated to %s\n"
                      uu____16154 uu____16155);
                   (let uu____16156 =
                      FStar_Syntax_Print.bvs_to_string ", " pat_bvs1  in
                    FStar_Util.print1 "pat_bvs = [%s]\n" uu____16156))
                else ());
               (let pat_env =
                  FStar_List.fold_left FStar_TypeChecker_Env.push_bv env
                    pat_bvs1
                   in
                let uu____16159 =
                  FStar_TypeChecker_Env.clear_expected_typ pat_env  in
                match uu____16159 with
                | (env1,uu____16181) ->
                    let env11 =
                      let uu___370_16187 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___370_16187.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___370_16187.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___370_16187.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___370_16187.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___370_16187.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___370_16187.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___370_16187.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___370_16187.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___370_16187.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___370_16187.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern = true;
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___370_16187.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___370_16187.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___370_16187.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___370_16187.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___370_16187.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___370_16187.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___370_16187.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___370_16187.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___370_16187.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___370_16187.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___370_16187.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___370_16187.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___370_16187.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___370_16187.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___370_16187.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___370_16187.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___370_16187.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___370_16187.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___370_16187.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___370_16187.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___370_16187.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___370_16187.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___370_16187.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___370_16187.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___370_16187.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___370_16187.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___370_16187.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___370_16187.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___370_16187.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___370_16187.FStar_TypeChecker_Env.dep_graph);
                        FStar_TypeChecker_Env.nbe =
                          (uu___370_16187.FStar_TypeChecker_Env.nbe)
                      }  in
                    let expected_pat_t =
                      FStar_TypeChecker_Rel.unrefine env pat_t  in
                    ((let uu____16190 =
                        FStar_TypeChecker_Env.debug env FStar_Options.High
                         in
                      if uu____16190
                      then
                        let uu____16191 =
                          FStar_Syntax_Print.term_to_string exp  in
                        let uu____16192 =
                          FStar_Syntax_Print.term_to_string pat_t  in
                        FStar_Util.print2
                          "Checking pattern expression %s against expected type %s\n"
                          uu____16191 uu____16192
                      else ());
                     (let env12 =
                        FStar_TypeChecker_Env.set_expected_typ env11
                          expected_pat_t
                         in
                      let uu____16195 = tc_tot_or_gtot_term env12 exp  in
                      match uu____16195 with
                      | (exp1,lc,g) ->
                          let g1 =
                            let uu___371_16220 = g  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___371_16220.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___371_16220.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___371_16220.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____16221 =
                            let uu____16222 =
                              FStar_TypeChecker_Rel.teq_nosmt_force env12
                                lc.FStar_Syntax_Syntax.res_typ expected_pat_t
                               in
                            if uu____16222
                            then
                              let env13 =
                                FStar_TypeChecker_Env.set_range env12
                                  exp1.FStar_Syntax_Syntax.pos
                                 in
                              let uu____16224 =
                                FStar_TypeChecker_Rel.discharge_guard_no_smt
                                  env13 g1
                                 in
                              FStar_All.pipe_right uu____16224
                                (FStar_TypeChecker_Rel.resolve_implicits
                                   env13)
                            else
                              (let uu____16226 =
                                 let uu____16231 =
                                   let uu____16232 =
                                     FStar_Syntax_Print.term_to_string
                                       lc.FStar_Syntax_Syntax.res_typ
                                      in
                                   let uu____16233 =
                                     FStar_Syntax_Print.term_to_string
                                       expected_pat_t
                                      in
                                   FStar_Util.format2
                                     "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                     uu____16232 uu____16233
                                    in
                                 (FStar_Errors.Fatal_MismatchedPatternType,
                                   uu____16231)
                                  in
                               FStar_Errors.raise_error uu____16226
                                 exp1.FStar_Syntax_Syntax.pos)
                             in
                          let norm_exp =
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env12 exp1
                             in
                          let uvs_to_string uvs =
                            let uu____16245 =
                              let uu____16248 = FStar_Util.set_elements uvs
                                 in
                              FStar_All.pipe_right uu____16248
                                (FStar_List.map
                                   (fun u  ->
                                      FStar_Syntax_Print.uvar_to_string
                                        u.FStar_Syntax_Syntax.ctx_uvar_head))
                               in
                            FStar_All.pipe_right uu____16245
                              (FStar_String.concat ", ")
                             in
                          let uvs1 = FStar_Syntax_Free.uvars norm_exp  in
                          let uvs2 = FStar_Syntax_Free.uvars expected_pat_t
                             in
                          ((let uu____16266 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Free")
                               in
                            if uu____16266
                            then
                              ((let uu____16268 =
                                  FStar_Syntax_Print.term_to_string norm_exp
                                   in
                                let uu____16269 = uvs_to_string uvs1  in
                                FStar_Util.print2 ">> free_1(%s) = %s\n"
                                  uu____16268 uu____16269);
                               (let uu____16270 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_pat_t
                                   in
                                let uu____16271 = uvs_to_string uvs2  in
                                FStar_Util.print2 ">> free_2(%s) = %s\n"
                                  uu____16270 uu____16271))
                            else ());
                           (let uu____16274 =
                              let uu____16275 =
                                FStar_Util.set_is_subset_of uvs1 uvs2  in
                              FStar_All.pipe_left Prims.op_Negation
                                uu____16275
                               in
                            if uu____16274
                            then
                              let unresolved =
                                FStar_Util.set_difference uvs1 uvs2  in
                              let uu____16279 =
                                let uu____16284 =
                                  let uu____16285 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env norm_exp
                                     in
                                  let uu____16286 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env expected_pat_t
                                     in
                                  let uu____16287 = uvs_to_string unresolved
                                     in
                                  FStar_Util.format3
                                    "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                    uu____16285 uu____16286 uu____16287
                                   in
                                (FStar_Errors.Fatal_UnresolvedPatternVar,
                                  uu____16284)
                                 in
                              FStar_Errors.raise_error uu____16279
                                p.FStar_Syntax_Syntax.p
                            else ());
                           (let uu____16290 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____16290
                            then
                              let uu____16291 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  env exp1
                                 in
                              FStar_Util.print1
                                "Done checking pattern expression %s\n"
                                uu____16291
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
        let uu____16338 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____16338 with
        | (pattern,when_clause,branch_exp) ->
            let uu____16383 = branch1  in
            (match uu____16383 with
             | (cpat,uu____16424,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____16446 =
                   let uu____16453 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____16453
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____16446 with
                  | (scrutinee_env,uu____16486) ->
                      let uu____16491 = tc_pat env true pat_t pattern  in
                      (match uu____16491 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____16541 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____16571 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____16571
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____16589 =
                                      let uu____16596 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____16596 e  in
                                    match uu____16589 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____16541 with
                            | (when_clause1,g_when) ->
                                let uu____16649 = tc_term pat_env branch_exp
                                   in
                                (match uu____16649 with
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
                                             let uu____16704 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_17  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_17) uu____16704
                                          in
                                       let uu____16715 =
                                         let eqs =
                                           let uu____16736 =
                                             let uu____16737 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____16737
                                              in
                                           if uu____16736
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____16750 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____16765 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____16768 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____16771 ->
                                                  let uu____16772 =
                                                    let uu____16775 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____16775 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____16772)
                                            in
                                         let uu____16778 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch1
                                            in
                                         match uu____16778 with
                                         | (c1,g_branch2) ->
                                             let uu____16803 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____16820 when
                                                   let uu____16833 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____16833
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
                                                   let uu____16863 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____16864 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____16863, uu____16864)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____16885 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____16885
                                                      in
                                                   let uu____16886 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____16887 =
                                                     let uu____16888 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____16888 g_when
                                                      in
                                                   (uu____16886, uu____16887)
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
                                                   let uu____16906 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____16906, g_when)
                                                in
                                             (match uu____16803 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return =
                                                    let c_weak1 =
                                                      let uu____16946 =
                                                        should_return &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____16946
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____16948 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____16948, g_branch2))
                                          in
                                       match uu____16715 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                           ->
                                           let branch_guard =
                                             let uu____16995 =
                                               let uu____16996 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____16996
                                                in
                                             if uu____16995
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____17038 =
                                                      let uu____17039 =
                                                        let uu____17040 =
                                                          let uu____17043 =
                                                            let uu____17050 =
                                                              FStar_TypeChecker_Env.typ_of_datacon
                                                                env
                                                                f.FStar_Syntax_Syntax.v
                                                               in
                                                            FStar_TypeChecker_Env.datacons_of_typ
                                                              env uu____17050
                                                             in
                                                          FStar_Pervasives_Native.snd
                                                            uu____17043
                                                           in
                                                        FStar_List.length
                                                          uu____17040
                                                         in
                                                      uu____17039 >
                                                        (Prims.parse_int "1")
                                                       in
                                                    if uu____17038
                                                    then
                                                      let discriminator =
                                                        FStar_Syntax_Util.mk_discriminator
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      let uu____17056 =
                                                        FStar_TypeChecker_Env.try_lookup_lid
                                                          env discriminator
                                                         in
                                                      match uu____17056 with
                                                      | FStar_Pervasives_Native.None
                                                           -> []
                                                      | uu____17077 ->
                                                          let disc =
                                                            FStar_Syntax_Syntax.fvar
                                                              discriminator
                                                              (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                 (Prims.parse_int "1"))
                                                              FStar_Pervasives_Native.None
                                                             in
                                                          let disc1 =
                                                            let uu____17092 =
                                                              let uu____17097
                                                                =
                                                                let uu____17098
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                   in
                                                                [uu____17098]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____17097
                                                               in
                                                            uu____17092
                                                              FStar_Pervasives_Native.None
                                                              scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                             in
                                                          let uu____17125 =
                                                            FStar_Syntax_Util.mk_eq2
                                                              FStar_Syntax_Syntax.U_zero
                                                              FStar_Syntax_Util.t_bool
                                                              disc1
                                                              FStar_Syntax_Util.exp_true_bool
                                                             in
                                                          [uu____17125]
                                                    else []  in
                                                  let fail1 uu____17132 =
                                                    let uu____17133 =
                                                      let uu____17134 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____17135 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____17136 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____17134
                                                        uu____17135
                                                        uu____17136
                                                       in
                                                    failwith uu____17133  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____17149) ->
                                                        head_constructor t1
                                                    | uu____17154 -> fail1 ()
                                                     in
                                                  let pat_exp2 =
                                                    let uu____17158 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____17158
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match pat_exp2.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      uu____17163 -> []
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_uvar
                                                           uu____17176;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu____17177;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu____17178;_},uu____17179)
                                                      -> []
                                                  | FStar_Syntax_Syntax.Tm_name
                                                      uu____17216 -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      (FStar_Const.Const_unit
                                                      ) -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      c1 ->
                                                      let uu____17218 =
                                                        let uu____17219 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____17219
                                                          scrutinee_tm1
                                                          pat_exp2
                                                         in
                                                      [uu____17218]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      uu____17220 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____17228 =
                                                        let uu____17229 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____17229
                                                         in
                                                      if uu____17228
                                                      then []
                                                      else
                                                        (let uu____17233 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____17233)
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      uu____17236 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____17238 =
                                                        let uu____17239 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____17239
                                                         in
                                                      if uu____17238
                                                      then []
                                                      else
                                                        (let uu____17243 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____17243)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,args) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____17273 =
                                                        let uu____17274 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____17274
                                                         in
                                                      if uu____17273
                                                      then []
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____17281 =
                                                             FStar_All.pipe_right
                                                               args
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____17317
                                                                     ->
                                                                    match uu____17317
                                                                    with
                                                                    | 
                                                                    (ei,uu____17329)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____17339
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____17339
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____17360
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____17374
                                                                    =
                                                                    let uu____17379
                                                                    =
                                                                    let uu____17380
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____17380
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____17381
                                                                    =
                                                                    let uu____17382
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____17382]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____17379
                                                                    uu____17381
                                                                     in
                                                                    uu____17374
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____17281
                                                             FStar_List.flatten
                                                            in
                                                         let uu____17415 =
                                                           discriminate
                                                             scrutinee_tm1 f
                                                            in
                                                         FStar_List.append
                                                           uu____17415
                                                           sub_term_guards)
                                                  | uu____17418 -> []  in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pat =
                                                  let uu____17434 =
                                                    let uu____17435 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____17435
                                                     in
                                                  if uu____17434
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____17438 =
                                                         build_branch_guard
                                                           scrutinee_tm1 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____17438
                                                        in
                                                     let uu____17447 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____17447 with
                                                     | (k,uu____17453) ->
                                                         let uu____17454 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____17454
                                                          with
                                                          | (t1,uu____17462,uu____17463)
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
                                           ((let uu____17475 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____17475
                                             then
                                               let uu____17476 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____17476
                                             else ());
                                            (let uu____17478 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____17495 =
                                               let uu____17496 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____17496 guard
                                                in
                                             (uu____17478, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____17495))))))))))

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
          let uu____17539 = check_let_bound_def true env1 lb  in
          (match uu____17539 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____17561 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____17582 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____17582, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____17587 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____17587
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____17589 =
                      let uu____17602 =
                        let uu____17617 =
                          let uu____17626 =
                            let uu____17633 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____17633)
                             in
                          [uu____17626]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____17617
                         in
                      FStar_List.hd uu____17602  in
                    match uu____17589 with
                    | (uu____17668,univs1,e11,c11,gvs) ->
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
                        let uu____17682 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____17682))
                  in
               (match uu____17561 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____17699 =
                      let uu____17708 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____17708
                      then
                        let uu____17717 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____17717 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____17746 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____17746
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____17747 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____17747, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____17761 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____17761
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____17767 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____17767
                            then e2
                            else
                              ((let uu____17772 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____17772
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
                    (match uu____17699 with
                     | (e21,c12) ->
                         ((let uu____17796 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____17796
                           then
                             let uu____17797 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____17797
                           else ());
                          (let e12 =
                             let uu____17800 = FStar_Options.tcnorm ()  in
                             if uu____17800
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
                           (let uu____17803 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____17803
                            then
                              let uu____17804 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____17804
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
                            let uu____17810 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____17821 =
                              FStar_Syntax_Util.lcomp_of_comp cres  in
                            (uu____17810, uu____17821,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____17822 -> failwith "Impossible"

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
            let uu___372_17853 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___372_17853.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___372_17853.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___372_17853.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___372_17853.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___372_17853.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___372_17853.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___372_17853.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___372_17853.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___372_17853.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___372_17853.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___372_17853.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___372_17853.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___372_17853.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___372_17853.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___372_17853.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___372_17853.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___372_17853.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___372_17853.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___372_17853.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___372_17853.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___372_17853.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___372_17853.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___372_17853.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___372_17853.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___372_17853.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___372_17853.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___372_17853.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___372_17853.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___372_17853.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___372_17853.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___372_17853.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___372_17853.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___372_17853.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___372_17853.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___372_17853.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___372_17853.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___372_17853.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___372_17853.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___372_17853.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___372_17853.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___372_17853.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____17854 =
            let uu____17865 =
              let uu____17866 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____17866 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____17865 lb  in
          (match uu____17854 with
           | (e1,uu____17888,c1,g1,annotated) ->
               ((let uu____17893 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____17897 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____17897)
                    in
                 if uu____17893
                 then
                   let uu____17898 =
                     let uu____17903 =
                       let uu____17904 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____17905 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____17904 uu____17905
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____17903)
                      in
                   FStar_Errors.raise_error uu____17898
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___373_17908 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___373_17908.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___373_17908.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____17909 =
                   let uu____17914 =
                     let uu____17915 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____17915]  in
                   FStar_Syntax_Subst.open_term uu____17914 e2  in
                 match uu____17909 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____17959 = tc_term env_x e21  in
                     (match uu____17959 with
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
                            let uu____17984 =
                              let uu____17991 =
                                let uu____17992 =
                                  let uu____18005 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____18005)  in
                                FStar_Syntax_Syntax.Tm_let uu____17992  in
                              FStar_Syntax_Syntax.mk uu____17991  in
                            uu____17984 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____18023 =
                              let uu____18024 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____18025 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____18024
                                c1.FStar_Syntax_Syntax.res_typ uu____18025
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_18  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_18)
                              uu____18023
                             in
                          let g21 =
                            let uu____18027 =
                              let uu____18028 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____18028 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____18027
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____18031 =
                            let uu____18032 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____18032  in
                          if uu____18031
                          then
                            let tt =
                              let uu____18042 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____18042
                                FStar_Option.get
                               in
                            ((let uu____18048 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____18048
                              then
                                let uu____18049 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____18050 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____18049 uu____18050
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____18053 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____18053 with
                             | (t,g_ex) ->
                                 ((let uu____18067 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____18067
                                   then
                                     let uu____18068 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____18069 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____18068 uu____18069
                                   else ());
                                  (let uu____18071 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___374_18073 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___374_18073.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___374_18073.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___374_18073.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____18071))))))))
      | uu____18074 ->
          failwith "Impossible (inner let with more than one lb)"

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
          let uu____18106 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____18106 with
           | (lbs1,e21) ->
               let uu____18125 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____18125 with
                | (env0,topt) ->
                    let uu____18144 = build_let_rec_env true env0 lbs1  in
                    (match uu____18144 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____18166 = check_let_recs rec_env lbs2  in
                         (match uu____18166 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____18186 =
                                  let uu____18187 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____18187
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____18186
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____18193 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____18193
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
                                     let uu____18242 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____18276 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____18276)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____18242
                                      in
                                   FStar_List.map2
                                     (fun uu____18310  ->
                                        fun lb  ->
                                          match uu____18310 with
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
                                let uu____18358 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____18358
                                 in
                              let uu____18359 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____18359 with
                               | (lbs5,e22) ->
                                   ((let uu____18379 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____18379
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____18380 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____18380, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____18391 -> failwith "Impossible"

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
          let uu____18423 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____18423 with
           | (lbs1,e21) ->
               let uu____18442 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____18442 with
                | (env0,topt) ->
                    let uu____18461 = build_let_rec_env false env0 lbs1  in
                    (match uu____18461 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____18483 =
                           let uu____18490 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____18490
                             (fun uu____18513  ->
                                match uu____18513 with
                                | (lbs3,g) ->
                                    let uu____18532 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____18532))
                            in
                         (match uu____18483 with
                          | (lbs3,g_lbs) ->
                              let uu____18547 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___375_18570 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___375_18570.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___375_18570.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___376_18572 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___376_18572.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____18547 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____18599 = tc_term env2 e21  in
                                   (match uu____18599 with
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
                                          let uu____18618 =
                                            let uu____18619 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____18619 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____18618
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
                                          let uu___377_18629 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___377_18629.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___377_18629.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___377_18629.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____18637 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____18637))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____18638 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____18638 with
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
                                                  uu____18676 ->
                                                  (e, cres4, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____18677 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____18677 with
                                                   | (tres1,g_ex) ->
                                                       let cres5 =
                                                         let uu___378_18691 =
                                                           cres4  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___378_18691.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___378_18691.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___378_18691.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____18692 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres5,
                                                         uu____18692))))))))))
      | uu____18693 -> failwith "Impossible"

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
          let uu____18738 = FStar_Options.ml_ish ()  in
          if uu____18738
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____18741 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____18741 with
             | (formals,c) ->
                 let uu____18772 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____18772 with
                  | (actuals,uu____18782,uu____18783) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____18800 =
                          let uu____18805 =
                            let uu____18806 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____18807 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____18806 uu____18807
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____18805)
                           in
                        FStar_Errors.raise_error uu____18800
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____18810 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____18810 actuals
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
                                (let uu____18837 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____18837)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____18857 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____18857)
                               in
                            let msg =
                              let uu____18865 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____18866 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____18865 uu____18866 formals_msg
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
        let uu____18873 =
          FStar_List.fold_left
            (fun uu____18906  ->
               fun lb  ->
                 match uu____18906 with
                 | (lbs1,env1,g_acc) ->
                     let uu____18931 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____18931 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____18951 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____18968 =
                                 let uu____18975 =
                                   let uu____18976 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____18976
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___379_18987 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___379_18987.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___379_18987.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___379_18987.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___379_18987.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___379_18987.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___379_18987.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___379_18987.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___379_18987.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___379_18987.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___379_18987.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___379_18987.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___379_18987.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___379_18987.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___379_18987.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___379_18987.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___379_18987.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___379_18987.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___379_18987.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___379_18987.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___379_18987.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___379_18987.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___379_18987.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___379_18987.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___379_18987.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___379_18987.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___379_18987.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___379_18987.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___379_18987.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___379_18987.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___379_18987.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___379_18987.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___379_18987.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___379_18987.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___379_18987.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___379_18987.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___379_18987.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___379_18987.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___379_18987.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___379_18987.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___379_18987.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___379_18987.FStar_TypeChecker_Env.nbe)
                                    }) t uu____18975
                                  in
                               match uu____18968 with
                               | (t1,uu____18995,g) ->
                                   let uu____18997 =
                                     let uu____18998 =
                                       let uu____18999 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____18999
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____18998
                                      in
                                   let uu____19000 = norm env01 t1  in
                                   (uu____18997, uu____19000))
                             in
                          (match uu____18951 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____19020 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____19020
                                 then
                                   let uu___380_19021 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___380_19021.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___380_19021.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___380_19021.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___380_19021.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___380_19021.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___380_19021.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___380_19021.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___380_19021.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___380_19021.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___380_19021.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___380_19021.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___380_19021.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___380_19021.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___380_19021.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___380_19021.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___380_19021.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___380_19021.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___380_19021.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___380_19021.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___380_19021.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___380_19021.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___380_19021.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___380_19021.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___380_19021.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___380_19021.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___380_19021.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___380_19021.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___380_19021.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___380_19021.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___380_19021.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___380_19021.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___380_19021.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___380_19021.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___380_19021.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___380_19021.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___380_19021.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___380_19021.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___380_19021.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___380_19021.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___380_19021.FStar_TypeChecker_Env.dep_graph);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___380_19021.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___381_19034 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___381_19034.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___381_19034.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___381_19034.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___381_19034.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____18873 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____19060 =
        let uu____19069 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____19095 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____19095 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____19125 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____19125
                       | uu____19130 ->
                           let lb1 =
                             let uu___382_19133 = lb  in
                             let uu____19134 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____19134;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___382_19133.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____19137 =
                             let uu____19144 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____19144
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____19137 with
                            | (e,c,g) ->
                                ((let uu____19153 =
                                    let uu____19154 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____19154  in
                                  if uu____19153
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
        FStar_All.pipe_right uu____19069 FStar_List.unzip  in
      match uu____19060 with
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
        let uu____19203 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____19203 with
        | (env1,uu____19221) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____19229 = check_lbtyp top_level env lb  in
            (match uu____19229 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____19273 =
                     tc_maybe_toplevel_term
                       (let uu___383_19282 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___383_19282.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___383_19282.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___383_19282.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___383_19282.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___383_19282.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___383_19282.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___383_19282.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___383_19282.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___383_19282.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___383_19282.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___383_19282.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___383_19282.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___383_19282.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___383_19282.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___383_19282.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___383_19282.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___383_19282.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___383_19282.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___383_19282.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___383_19282.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___383_19282.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___383_19282.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___383_19282.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___383_19282.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___383_19282.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___383_19282.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___383_19282.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___383_19282.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___383_19282.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___383_19282.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___383_19282.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___383_19282.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___383_19282.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___383_19282.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___383_19282.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___383_19282.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___383_19282.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___383_19282.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___383_19282.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___383_19282.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___383_19282.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____19273 with
                   | (e12,c1,g1) ->
                       let uu____19296 =
                         let uu____19301 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____19306  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____19301 e12 c1 wf_annot
                          in
                       (match uu____19296 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____19321 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____19321
                              then
                                let uu____19322 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____19323 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____19324 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____19322 uu____19323 uu____19324
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
            let uu____19358 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____19358 with
             | (univ_opening,univ_vars1) ->
                 let uu____19391 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____19391))
        | uu____19396 ->
            let uu____19397 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____19397 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____19446 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____19446)
                 else
                   (let uu____19452 = FStar_Syntax_Util.type_u ()  in
                    match uu____19452 with
                    | (k,uu____19472) ->
                        let uu____19473 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____19473 with
                         | (t2,uu____19495,g) ->
                             ((let uu____19498 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____19498
                               then
                                 let uu____19499 =
                                   let uu____19500 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____19500
                                    in
                                 let uu____19501 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____19499 uu____19501
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____19504 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____19504))))))

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
    fun uu____19510  ->
      match uu____19510 with
      | (x,imp) ->
          let uu____19537 = FStar_Syntax_Util.type_u ()  in
          (match uu____19537 with
           | (tu,u) ->
               ((let uu____19559 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____19559
                 then
                   let uu____19560 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____19561 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____19562 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____19560 uu____19561 uu____19562
                 else ());
                (let uu____19564 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____19564 with
                 | (t,uu____19586,g) ->
                     let x1 =
                       ((let uu___384_19598 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___384_19598.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___384_19598.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____19600 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____19600
                       then
                         let uu____19601 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____19604 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____19601 uu____19604
                       else ());
                      (let uu____19606 = push_binding env x1  in
                       (x1, uu____19606, g, u))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun bs  ->
      (let uu____19618 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____19618
       then
         let uu____19619 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____19619
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____19728 = tc_binder env1 b  in
             (match uu____19728 with
              | (b1,env',g,u) ->
                  let uu____19777 = aux env' bs2  in
                  (match uu____19777 with
                   | (bs3,env'1,g',us) ->
                       let uu____19838 =
                         let uu____19839 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____19839  in
                       ((b1 :: bs3), env'1, uu____19838, (u :: us))))
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
          (fun uu____19946  ->
             fun uu____19947  ->
               match (uu____19946, uu____19947) with
               | ((t,imp),(args1,g)) ->
                   let uu____20038 = tc_term env1 t  in
                   (match uu____20038 with
                    | (t1,uu____20058,g') ->
                        let uu____20060 =
                          FStar_TypeChecker_Env.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____20060))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____20114  ->
             match uu____20114 with
             | (pats1,g) ->
                 let uu____20141 = tc_args env p  in
                 (match uu____20141 with
                  | (args,g') ->
                      let uu____20154 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____20154))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____20167 = tc_maybe_toplevel_term env e  in
      match uu____20167 with
      | (e1,c,g) ->
          let uu____20183 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____20183
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____20194 =
               let uu____20199 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____20199
               then
                 let uu____20204 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____20204, false)
               else
                 (let uu____20206 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____20206, true))
                in
             match uu____20194 with
             | (target_comp,allow_ghost) ->
                 let uu____20215 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____20215 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____20225 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____20226 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____20225, uu____20226)
                  | uu____20227 ->
                      if allow_ghost
                      then
                        let uu____20236 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____20236
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____20248 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____20248
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
      let uu____20271 = tc_tot_or_gtot_term env t  in
      match uu____20271 with
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
      (let uu____20303 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____20303
       then
         let uu____20304 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____20304
       else ());
      (let env1 =
         let uu___385_20307 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___385_20307.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___385_20307.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___385_20307.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___385_20307.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___385_20307.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___385_20307.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___385_20307.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___385_20307.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___385_20307.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___385_20307.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___385_20307.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___385_20307.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___385_20307.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___385_20307.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___385_20307.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___385_20307.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___385_20307.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___385_20307.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___385_20307.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___385_20307.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___385_20307.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___385_20307.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___385_20307.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___385_20307.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___385_20307.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___385_20307.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___385_20307.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___385_20307.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___385_20307.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___385_20307.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___385_20307.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___385_20307.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___385_20307.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___385_20307.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___385_20307.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___385_20307.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___385_20307.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___385_20307.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___385_20307.FStar_TypeChecker_Env.dep_graph);
           FStar_TypeChecker_Env.nbe =
             (uu___385_20307.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____20314 =
         try
           (fun uu___387_20328  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____20349) ->
             let uu____20350 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____20350
          in
       match uu____20314 with
       | (t,c,g) ->
           let uu____20366 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____20366
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____20374 =
                let uu____20379 =
                  let uu____20380 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____20380
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____20379)
                 in
              let uu____20381 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____20374 uu____20381))
  
let level_of_type_fail :
  'Auu____20396 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____20396
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____20412 =
          let uu____20417 =
            let uu____20418 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____20418 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____20417)  in
        let uu____20419 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____20412 uu____20419
  
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
          let uu____20454 =
            let uu____20455 = FStar_Syntax_Util.unrefine t1  in
            uu____20455.FStar_Syntax_Syntax.n  in
          match uu____20454 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____20459 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____20462 = FStar_Syntax_Util.type_u ()  in
                 match uu____20462 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___388_20470 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___388_20470.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___388_20470.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___388_20470.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___388_20470.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___388_20470.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___388_20470.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___388_20470.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___388_20470.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___388_20470.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___388_20470.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___388_20470.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___388_20470.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___388_20470.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___388_20470.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___388_20470.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___388_20470.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___388_20470.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___388_20470.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___388_20470.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___388_20470.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___388_20470.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___388_20470.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___388_20470.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___388_20470.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___388_20470.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___388_20470.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___388_20470.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___388_20470.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___388_20470.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___388_20470.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___388_20470.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___388_20470.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___388_20470.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___388_20470.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___388_20470.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___388_20470.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___388_20470.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___388_20470.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___388_20470.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___388_20470.FStar_TypeChecker_Env.dep_graph);
                         FStar_TypeChecker_Env.nbe =
                           (uu___388_20470.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____20474 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____20474
                       | uu____20475 ->
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
      let uu____20492 =
        let uu____20493 = FStar_Syntax_Subst.compress e  in
        uu____20493.FStar_Syntax_Syntax.n  in
      match uu____20492 with
      | FStar_Syntax_Syntax.Tm_bvar uu____20498 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____20503 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____20528 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____20544) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____20590) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____20597 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20597 with | ((uu____20608,t),uu____20610) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____20616 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____20616
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20619,(FStar_Util.Inl t,uu____20621),uu____20622) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20669,(FStar_Util.Inr c,uu____20671),uu____20672) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____20720 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____20729;
             FStar_Syntax_Syntax.vars = uu____20730;_},us)
          ->
          let uu____20736 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20736 with
           | ((us',t),uu____20749) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____20755 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____20755)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____20771 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____20772 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____20782) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____20809 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____20809 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____20831  ->
                      match uu____20831 with
                      | (b,uu____20839) ->
                          let uu____20844 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____20844) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____20851 = universe_of_aux env res  in
                 level_of_type env res uu____20851  in
               let u_c =
                 let uu____20855 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____20855 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____20859 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____20859
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
            | FStar_Syntax_Syntax.Tm_bvar uu____20974 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____20991 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____21030 ->
                let uu____21031 = universe_of_aux env hd3  in
                (uu____21031, args1)
            | FStar_Syntax_Syntax.Tm_name uu____21046 ->
                let uu____21047 = universe_of_aux env hd3  in
                (uu____21047, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____21062 ->
                let uu____21075 = universe_of_aux env hd3  in
                (uu____21075, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____21090 ->
                let uu____21097 = universe_of_aux env hd3  in
                (uu____21097, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____21112 ->
                let uu____21139 = universe_of_aux env hd3  in
                (uu____21139, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____21154 ->
                let uu____21161 = universe_of_aux env hd3  in
                (uu____21161, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____21176 ->
                let uu____21177 = universe_of_aux env hd3  in
                (uu____21177, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____21192 ->
                let uu____21207 = universe_of_aux env hd3  in
                (uu____21207, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____21222 ->
                let uu____21229 = universe_of_aux env hd3  in
                (uu____21229, args1)
            | FStar_Syntax_Syntax.Tm_type uu____21244 ->
                let uu____21245 = universe_of_aux env hd3  in
                (uu____21245, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____21260,hd4::uu____21262) ->
                let uu____21327 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____21327 with
                 | (uu____21344,uu____21345,hd5) ->
                     let uu____21363 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____21363 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____21422 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____21424 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____21424 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____21483 ->
                let uu____21484 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____21484 with
                 | (env1,uu____21508) ->
                     let env2 =
                       let uu___389_21514 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___389_21514.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___389_21514.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___389_21514.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___389_21514.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___389_21514.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___389_21514.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___389_21514.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___389_21514.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___389_21514.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___389_21514.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___389_21514.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___389_21514.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___389_21514.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___389_21514.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___389_21514.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___389_21514.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___389_21514.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___389_21514.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___389_21514.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___389_21514.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___389_21514.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___389_21514.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___389_21514.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___389_21514.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___389_21514.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___389_21514.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___389_21514.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___389_21514.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___389_21514.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___389_21514.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___389_21514.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___389_21514.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___389_21514.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___389_21514.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___389_21514.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___389_21514.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___389_21514.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___389_21514.FStar_TypeChecker_Env.dep_graph);
                         FStar_TypeChecker_Env.nbe =
                           (uu___389_21514.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____21516 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____21516
                       then
                         let uu____21517 =
                           let uu____21518 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____21518  in
                         let uu____21519 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____21517 uu____21519
                       else ());
                      (let uu____21521 = tc_term env2 hd3  in
                       match uu____21521 with
                       | (uu____21544,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____21545;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____21547;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____21548;_},g)
                           ->
                           ((let uu____21562 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____21562
                               (fun a236  -> ()));
                            (t, args1)))))
             in
          let uu____21575 = type_of_head true hd1 args  in
          (match uu____21575 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____21621 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____21621 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____21675 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____21675)))
      | FStar_Syntax_Syntax.Tm_match (uu____21678,hd1::uu____21680) ->
          let uu____21745 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____21745 with
           | (uu____21748,uu____21749,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____21767,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____21814 = universe_of_aux env e  in
      level_of_type env e uu____21814
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____21839 = tc_binders env tps  in
      match uu____21839 with
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
      let uu____21893 =
        let uu____21894 = FStar_Syntax_Subst.compress t  in
        uu____21894.FStar_Syntax_Syntax.n  in
      match uu____21893 with
      | FStar_Syntax_Syntax.Tm_delayed uu____21899 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____21924 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____21929 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____21929
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____21931 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21931
            (fun uu____21945  ->
               match uu____21945 with
               | (t1,uu____21953) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____21955;
             FStar_Syntax_Syntax.vars = uu____21956;_},us)
          ->
          let uu____21962 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21962
            (fun uu____21976  ->
               match uu____21976 with
               | (t1,uu____21984) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____21986 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____21986
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____21988 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____21988
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____21993;_})
          ->
          let mk_comp =
            let uu____22037 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____22037
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____22065 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____22065
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____22132 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____22132
                 (fun u  ->
                    let uu____22140 =
                      let uu____22143 =
                        let uu____22150 =
                          let uu____22151 =
                            let uu____22166 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____22166)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____22151  in
                        FStar_Syntax_Syntax.mk uu____22150  in
                      uu____22143 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____22140))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____22206 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____22206 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____22265 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____22265
                       (fun uc  ->
                          let uu____22273 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____22273)
                 | (x,imp)::bs3 ->
                     let uu____22299 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____22299
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____22308 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____22328) ->
          let uu____22333 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____22333
            (fun u_x  ->
               let uu____22341 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____22341)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____22387 =
              let uu____22388 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____22388.FStar_Syntax_Syntax.n  in
            match uu____22387 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____22470 = FStar_Util.first_N n_args bs  in
                    match uu____22470 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____22562 =
                          let uu____22567 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____22567  in
                        (match uu____22562 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____22627 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____22627 with
                       | (bs1,c1) ->
                           let uu____22648 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____22648
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____22726  ->
                     match uu____22726 with
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
                         let uu____22802 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____22802)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____22804) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____22810,uu____22811) ->
                aux t1
            | uu____22852 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22853,(FStar_Util.Inl t1,uu____22855),uu____22856) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22903,(FStar_Util.Inr c,uu____22905),uu____22906) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____22971 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____22971
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____22979) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____22984 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____23007 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____23020 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____23031 = type_of_well_typed_term env t  in
      match uu____23031 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____23037;
            FStar_Syntax_Syntax.vars = uu____23038;_}
          -> FStar_Pervasives_Native.Some u
      | uu____23041 -> FStar_Pervasives_Native.None

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
            let uu___390_23066 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___390_23066.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___390_23066.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___390_23066.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___390_23066.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___390_23066.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___390_23066.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___390_23066.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___390_23066.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___390_23066.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___390_23066.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___390_23066.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___390_23066.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___390_23066.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___390_23066.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___390_23066.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___390_23066.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___390_23066.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___390_23066.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___390_23066.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___390_23066.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___390_23066.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___390_23066.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___390_23066.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___390_23066.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___390_23066.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___390_23066.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___390_23066.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___390_23066.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___390_23066.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___390_23066.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___390_23066.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___390_23066.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___390_23066.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___390_23066.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___390_23066.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___390_23066.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___390_23066.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___390_23066.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___390_23066.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___390_23066.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___390_23066.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____23072 =
            if must_total
            then
              let uu____23073 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____23073 with | (uu____23080,uu____23081,g) -> g
            else
              (let uu____23084 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____23084 with | (uu____23091,uu____23092,g) -> g)
             in
          let uu____23094 = type_of_well_typed_term env2 t  in
          match uu____23094 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____23099 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____23099
                then
                  let uu____23100 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____23101 = FStar_Syntax_Print.term_to_string t  in
                  let uu____23102 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____23103 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____23100 uu____23101 uu____23102 uu____23103
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____23109 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____23109
                 then
                   let uu____23110 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____23111 = FStar_Syntax_Print.term_to_string t  in
                   let uu____23112 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____23113 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____23110
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____23111 uu____23112 uu____23113
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
            let uu___391_23139 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___391_23139.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___391_23139.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___391_23139.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___391_23139.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___391_23139.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___391_23139.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___391_23139.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___391_23139.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___391_23139.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___391_23139.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___391_23139.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___391_23139.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___391_23139.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___391_23139.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___391_23139.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___391_23139.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___391_23139.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___391_23139.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___391_23139.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___391_23139.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___391_23139.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___391_23139.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___391_23139.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___391_23139.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___391_23139.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___391_23139.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___391_23139.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___391_23139.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___391_23139.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___391_23139.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___391_23139.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___391_23139.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___391_23139.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___391_23139.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___391_23139.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___391_23139.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___391_23139.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___391_23139.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___391_23139.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___391_23139.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___391_23139.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____23145 =
            if must_total
            then
              let uu____23146 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____23146 with | (uu____23153,uu____23154,g) -> g
            else
              (let uu____23157 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____23157 with | (uu____23164,uu____23165,g) -> g)
             in
          let uu____23167 =
            let uu____23168 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____23168  in
          if uu____23167
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  