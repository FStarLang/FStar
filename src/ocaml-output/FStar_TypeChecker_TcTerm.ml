open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___332_6 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___332_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___332_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___332_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___332_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___332_6.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___332_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___332_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___332_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___332_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___332_6.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___332_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___332_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___332_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___332_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___332_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___332_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___332_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___332_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___332_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___332_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___332_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___332_6.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___332_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___332_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___332_6.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___332_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___332_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___332_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___332_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___332_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___332_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___332_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___332_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___332_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___332_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___332_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___332_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___332_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___332_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___332_6.FStar_TypeChecker_Env.dep_graph)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___333_12 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___333_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___333_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___333_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___333_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___333_12.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___333_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___333_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___333_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___333_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___333_12.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___333_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___333_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___333_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___333_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___333_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___333_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___333_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___333_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___333_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___333_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___333_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___333_12.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___333_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___333_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___333_12.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___333_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___333_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___333_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___333_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___333_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___333_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___333_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___333_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___333_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___333_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___333_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___333_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___333_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___333_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___333_12.FStar_TypeChecker_Env.dep_graph)
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
  fun uu___326_113  ->
    match uu___326_113 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____116 -> false
  
let steps :
  'Auu____123 . 'Auu____123 -> FStar_TypeChecker_Normalize.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.NoFullNorm]
  
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
                [FStar_TypeChecker_Normalize.Beta] env pats
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
              let uu___334_1452 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___334_1452.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___334_1452.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___334_1452.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___334_1452.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___334_1452.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___334_1452.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___334_1452.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___334_1452.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___334_1452.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___334_1452.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___334_1452.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___334_1452.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___334_1452.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___334_1452.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___334_1452.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___334_1452.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___334_1452.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___334_1452.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___334_1452.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___334_1452.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___334_1452.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___334_1452.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___334_1452.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___334_1452.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___334_1452.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___334_1452.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___334_1452.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___334_1452.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___334_1452.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___334_1452.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___334_1452.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___334_1452.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___334_1452.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___334_1452.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___334_1452.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___334_1452.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___334_1452.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___334_1452.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___334_1452.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___334_1452.FStar_TypeChecker_Env.dep_graph)
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
                      (fun uu___327_1625  ->
                         match uu___327_1625 with
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
                                   let uu___335_1950 = last1  in
                                   let uu____1951 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___335_1950.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___335_1950.FStar_Syntax_Syntax.index);
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
      let uu____2614 =
        FStar_Util.record_time
          (fun uu____2632  ->
             tc_maybe_toplevel_term
               (let uu___336_2635 = env  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___336_2635.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___336_2635.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___336_2635.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___336_2635.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___336_2635.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___336_2635.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___336_2635.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___336_2635.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___336_2635.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___336_2635.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___336_2635.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___336_2635.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___336_2635.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___336_2635.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___336_2635.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level = false;
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___336_2635.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___336_2635.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___336_2635.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___336_2635.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___336_2635.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___336_2635.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___336_2635.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___336_2635.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___336_2635.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___336_2635.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___336_2635.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___336_2635.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___336_2635.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___336_2635.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___336_2635.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___336_2635.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___336_2635.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___336_2635.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___336_2635.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___336_2635.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___336_2635.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___336_2635.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___336_2635.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___336_2635.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___336_2635.FStar_TypeChecker_Env.dep_graph)
                }) e)
         in
      match uu____2614 with
      | (r,ms) ->
          ((let uu____2657 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____2657
            then
              let uu____2658 =
                let uu____2659 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left FStar_Range.string_of_range uu____2659
                 in
              let uu____2660 = FStar_Syntax_Print.term_to_string e  in
              let uu____2661 =
                let uu____2662 = FStar_Syntax_Subst.compress e  in
                FStar_Syntax_Print.tag_of_term uu____2662  in
              let uu____2663 = FStar_Util.string_of_int ms  in
              FStar_Util.print4 "(%s) tc_term of %s (%s) took %sms\n"
                uu____2658 uu____2660 uu____2661 uu____2663
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
      (let uu____2677 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2677
       then
         let uu____2678 =
           let uu____2679 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2679  in
         let uu____2680 = FStar_Syntax_Print.tag_of_term top  in
         let uu____2681 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2678 uu____2680
           uu____2681
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2689 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2718 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2725 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2738 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2739 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2740 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2741 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2742 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2761 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2776 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2783 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted
           (uu____2784,{
                         FStar_Syntax_Syntax.qkind =
                           FStar_Syntax_Syntax.Quote_static ;
                         FStar_Syntax_Syntax.antiquotes = aqs;_})
           when
           FStar_List.for_all
             (fun uu____2812  ->
                match uu____2812 with
                | (uu____2821,b,uu____2823) -> Prims.op_Negation b) aqs
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_quoted uu____2828 ->
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
           let uu____2844 =
             let uu____2851 =
               let uu____2856 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____2856  in
             value_check_expected_typ env1 top uu____2851
               FStar_TypeChecker_Env.trivial_guard
              in
           (match uu____2844 with
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
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.typ))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____2879 = tc_tot_or_gtot_term env1 e1  in
           (match uu____2879 with
            | (e2,c,g) ->
                let g1 =
                  let uu___337_2896 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___337_2896.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___337_2896.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___337_2896.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____2897 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____2897, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2918 = FStar_Syntax_Util.type_u ()  in
           (match uu____2918 with
            | (t,u) ->
                let uu____2931 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____2931 with
                 | (e2,c,g) ->
                     let uu____2947 =
                       let uu____2964 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2964 with
                       | (env2,uu____2988) -> tc_pats env2 pats  in
                     (match uu____2947 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___338_3026 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___338_3026.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___338_3026.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___338_3026.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____3027 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____3030 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____3027, c, uu____3030))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____3036 =
             let uu____3037 = FStar_Syntax_Subst.compress e1  in
             uu____3037.FStar_Syntax_Syntax.n  in
           (match uu____3036 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____3046,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____3048;
                               FStar_Syntax_Syntax.lbtyp = uu____3049;
                               FStar_Syntax_Syntax.lbeff = uu____3050;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____3052;
                               FStar_Syntax_Syntax.lbpos = uu____3053;_}::[]),e2)
                ->
                let uu____3081 =
                  let uu____3088 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____3088 e11  in
                (match uu____3081 with
                 | (e12,c1,g1) ->
                     let uu____3098 = tc_term env1 e2  in
                     (match uu____3098 with
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
                            let uu____3122 =
                              let uu____3129 =
                                let uu____3130 =
                                  let uu____3143 =
                                    let uu____3150 =
                                      let uu____3153 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____3153]  in
                                    (false, uu____3150)  in
                                  (uu____3143, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____3130  in
                              FStar_Syntax_Syntax.mk uu____3129  in
                            uu____3122 FStar_Pervasives_Native.None
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
                          let uu____3175 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____3175)))
            | uu____3176 ->
                let uu____3177 = tc_term env1 e1  in
                (match uu____3177 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____3199) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____3211) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____3230 = tc_term env1 e1  in
           (match uu____3230 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____3254) ->
           let uu____3301 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____3301 with
            | (env0,uu____3315) ->
                let uu____3320 = tc_comp env0 expected_c  in
                (match uu____3320 with
                 | (expected_c1,uu____3334,g) ->
                     let uu____3336 =
                       let uu____3343 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____3343 e1  in
                     (match uu____3336 with
                      | (e2,c',g') ->
                          let uu____3353 =
                            let uu____3360 =
                              let uu____3365 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____3365)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____3360
                             in
                          (match uu____3353 with
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
                                 let uu____3419 =
                                   FStar_TypeChecker_Env.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Env.conj_guard g
                                   uu____3419
                                  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Env.map_guard f
                                       (fun f1  ->
                                          let uu____3425 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____3425)
                                  in
                               let uu____3426 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____3426 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Env.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____3446) ->
           let uu____3493 = FStar_Syntax_Util.type_u ()  in
           (match uu____3493 with
            | (k,u) ->
                let uu____3506 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____3506 with
                 | (t1,uu____3520,f) ->
                     let uu____3522 =
                       let uu____3529 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____3529 e1  in
                     (match uu____3522 with
                      | (e2,c,g) ->
                          let uu____3539 =
                            let uu____3544 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____3549  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____3544 e2 c f
                             in
                          (match uu____3539 with
                           | (c1,f1) ->
                               let uu____3558 =
                                 let uu____3565 =
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
                                 comp_check_expected_typ env1 uu____3565 c1
                                  in
                               (match uu____3558 with
                                | (e3,c2,f2) ->
                                    let uu____3613 =
                                      let uu____3614 =
                                        FStar_TypeChecker_Env.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____3614
                                       in
                                    (e3, c2, uu____3613))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3615;
              FStar_Syntax_Syntax.vars = uu____3616;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3695 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3695 with
            | (unary_op,uu____3719) ->
                let head1 =
                  let uu____3747 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3747
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
              FStar_Syntax_Syntax.pos = uu____3795;
              FStar_Syntax_Syntax.vars = uu____3796;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3875 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3875 with
            | (unary_op,uu____3899) ->
                let head1 =
                  let uu____3927 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3927
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
                (FStar_Const.Const_reflect uu____3975);
              FStar_Syntax_Syntax.pos = uu____3976;
              FStar_Syntax_Syntax.vars = uu____3977;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4056 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4056 with
            | (unary_op,uu____4080) ->
                let head1 =
                  let uu____4108 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____4108
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
              FStar_Syntax_Syntax.pos = uu____4156;
              FStar_Syntax_Syntax.vars = uu____4157;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____4253 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4253 with
            | (unary_op,uu____4277) ->
                let head1 =
                  let uu____4305 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____4305
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
              FStar_Syntax_Syntax.pos = uu____4361;
              FStar_Syntax_Syntax.vars = uu____4362;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____4400 =
             let uu____4407 =
               let uu____4408 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4408  in
             tc_term uu____4407 e1  in
           (match uu____4400 with
            | (e2,c,g) ->
                let uu____4432 = FStar_Syntax_Util.head_and_args top  in
                (match uu____4432 with
                 | (head1,uu____4456) ->
                     let uu____4481 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____4514 =
                       let uu____4515 =
                         let uu____4516 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____4516  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4515
                        in
                     (uu____4481, uu____4514, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4517;
              FStar_Syntax_Syntax.vars = uu____4518;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____4571 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4571 with
            | (head1,uu____4595) ->
                let env' =
                  let uu____4621 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____4621  in
                let uu____4622 = tc_term env' r  in
                (match uu____4622 with
                 | (er,uu____4636,gr) ->
                     let uu____4638 = tc_term env1 t  in
                     (match uu____4638 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____4655 =
                            let uu____4656 =
                              let uu____4661 =
                                let uu____4662 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____4671 =
                                  let uu____4682 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____4682]  in
                                uu____4662 :: uu____4671  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____4661
                               in
                            uu____4656 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____4655, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____4717;
              FStar_Syntax_Syntax.vars = uu____4718;_},uu____4719)
           ->
           let uu____4744 =
             let uu____4749 =
               let uu____4750 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4750  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4749)  in
           FStar_Errors.raise_error uu____4744 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4757;
              FStar_Syntax_Syntax.vars = uu____4758;_},uu____4759)
           ->
           let uu____4784 =
             let uu____4789 =
               let uu____4790 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4790  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4789)  in
           FStar_Errors.raise_error uu____4784 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____4797;
              FStar_Syntax_Syntax.vars = uu____4798;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____4841 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____4841 with
             | (env0,uu____4855) ->
                 let uu____4860 = tc_term env0 e1  in
                 (match uu____4860 with
                  | (e2,c,g) ->
                      let uu____4876 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____4876 with
                       | (reify_op,uu____4900) ->
                           let u_c =
                             let uu____4926 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____4926 with
                             | (uu____4933,c',uu____4935) ->
                                 let uu____4936 =
                                   let uu____4937 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____4937.FStar_Syntax_Syntax.n  in
                                 (match uu____4936 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____4941 ->
                                      let uu____4942 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____4942 with
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
                                                 let uu____4954 =
                                                   let uu____4955 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____4956 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____4957 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____4955 uu____4956
                                                     uu____4957
                                                    in
                                                 failwith uu____4954);
                                            u)))
                              in
                           let repr =
                             let uu____4959 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____4959
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
                             let uu____4996 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____4996
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____4997 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____4997 with
                            | (e4,c2,g') ->
                                let uu____5013 =
                                  FStar_TypeChecker_Env.conj_guard g g'  in
                                (e4, c2, uu____5013))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____5015;
              FStar_Syntax_Syntax.vars = uu____5016;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____5070 =
               let uu____5071 =
                 let uu____5076 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____5076)  in
               FStar_Errors.raise_error uu____5071 e1.FStar_Syntax_Syntax.pos
                in
             let uu____5083 = FStar_Syntax_Util.head_and_args top  in
             match uu____5083 with
             | (reflect_op,uu____5107) ->
                 let uu____5132 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____5132 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____5165 =
                        let uu____5166 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____5166  in
                      if uu____5165
                      then no_reflect ()
                      else
                        (let uu____5176 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____5176 with
                         | (env_no_ex,topt) ->
                             let uu____5195 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____5215 =
                                   let uu____5222 =
                                     let uu____5223 =
                                       let uu____5240 =
                                         let uu____5251 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____5260 =
                                           let uu____5271 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____5271]  in
                                         uu____5251 :: uu____5260  in
                                       (repr, uu____5240)  in
                                     FStar_Syntax_Syntax.Tm_app uu____5223
                                      in
                                   FStar_Syntax_Syntax.mk uu____5222  in
                                 uu____5215 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____5319 =
                                 let uu____5326 =
                                   let uu____5327 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____5327
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____5326 t  in
                               match uu____5319 with
                               | (t1,uu____5353,g) ->
                                   let uu____5355 =
                                     let uu____5356 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____5356.FStar_Syntax_Syntax.n  in
                                   (match uu____5355 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____5369,(res,uu____5371)::
                                         (wp,uu____5373)::[])
                                        -> (t1, res, wp, g)
                                    | uu____5430 -> failwith "Impossible")
                                in
                             (match uu____5195 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____5455 =
                                    let uu____5462 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____5462 with
                                    | (e2,c,g) ->
                                        ((let uu____5479 =
                                            let uu____5480 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____5480
                                             in
                                          if uu____5479
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____5494 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____5494 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____5504 =
                                                  let uu____5513 =
                                                    let uu____5520 =
                                                      let uu____5521 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____5522 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____5521 uu____5522
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____5520,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____5513]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____5504);
                                               (let uu____5535 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____5535)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____5539 =
                                                let uu____5540 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g' uu____5540
                                                 in
                                              (e2, uu____5539)))
                                     in
                                  (match uu____5455 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____5556 =
                                           let uu____5557 =
                                             let uu____5558 =
                                               let uu____5559 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____5559]  in
                                             let uu____5560 =
                                               let uu____5571 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____5571]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____5558;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____5560;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____5557
                                            in
                                         FStar_All.pipe_right uu____5556
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____5631 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____5631 with
                                        | (e4,c1,g') ->
                                            let uu____5647 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____5647))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5686 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5686 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____5736,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____5737))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5789 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5789 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____5864 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____6073 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____5864 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____6190 =
               let uu____6191 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____6191 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____6190 instantiate_both  in
           ((let uu____6207 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____6207
             then
               let uu____6208 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____6209 = FStar_Syntax_Print.term_to_string top  in
               let uu____6210 =
                 let uu____6211 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____6211
                   (fun uu___328_6217  ->
                      match uu___328_6217 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____6208
                 uu____6209 uu____6210
             else ());
            (let uu____6222 = tc_term (no_inst env2) head1  in
             match uu____6222 with
             | (head2,chead,g_head) ->
                 let uu____6238 =
                   let uu____6245 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____6247 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____6247))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____6245
                   then
                     let uu____6254 =
                       let uu____6261 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____6261
                        in
                     match uu____6254 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____6274 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____6274)
                    in
                 (match uu____6238 with
                  | (e1,c,g) ->
                      ((let uu____6287 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____6287
                        then
                          let uu____6288 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____6288
                        else ());
                       (let uu____6290 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____6290 with
                        | (e2,c1,g') ->
                            let gres = FStar_TypeChecker_Env.conj_guard g g'
                               in
                            ((let uu____6308 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____6308
                              then
                                let uu____6309 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____6310 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____6309 uu____6310
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____6350 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____6350 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____6370 = tc_term env12 e1  in
                (match uu____6370 with
                 | (e11,c1,g1) ->
                     let uu____6386 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____6400 = FStar_Syntax_Util.type_u ()  in
                           (match uu____6400 with
                            | (k,uu____6412) ->
                                let uu____6413 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____6413 with
                                 | (res_t,uu____6433,g) ->
                                     let uu____6447 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____6448 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____6447, res_t, uu____6448)))
                        in
                     (match uu____6386 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____6459 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____6459
                            then
                              let uu____6460 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____6460
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
                            let uu____6581 =
                              let uu____6586 =
                                FStar_List.fold_right
                                  (fun uu____6665  ->
                                     fun uu____6666  ->
                                       match (uu____6665, uu____6666) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____6900 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____6900)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____6586 with
                              | (cases,g) ->
                                  let uu____6998 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____6998, g)
                               in
                            match uu____6581 with
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
                                           (fun uu____7138  ->
                                              match uu____7138 with
                                              | ((pat,wopt,br),uu____7182,eff_label,uu____7184,uu____7185,uu____7186)
                                                  ->
                                                  let uu____7221 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____7221)))
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
                                  let uu____7288 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____7288
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____7293 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____7293  in
                                     let lb =
                                       let uu____7297 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____7297 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____7303 =
                                         let uu____7310 =
                                           let uu____7311 =
                                             let uu____7324 =
                                               let uu____7327 =
                                                 let uu____7328 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____7328]  in
                                               FStar_Syntax_Subst.close
                                                 uu____7327 e_match
                                                in
                                             ((false, [lb]), uu____7324)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____7311
                                            in
                                         FStar_Syntax_Syntax.mk uu____7310
                                          in
                                       uu____7303
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____7361 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____7361
                                  then
                                    let uu____7362 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7363 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____7362 uu____7363
                                  else ());
                                 (let uu____7365 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____7365))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7366;
                FStar_Syntax_Syntax.lbunivs = uu____7367;
                FStar_Syntax_Syntax.lbtyp = uu____7368;
                FStar_Syntax_Syntax.lbeff = uu____7369;
                FStar_Syntax_Syntax.lbdef = uu____7370;
                FStar_Syntax_Syntax.lbattrs = uu____7371;
                FStar_Syntax_Syntax.lbpos = uu____7372;_}::[]),uu____7373)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____7396),uu____7397) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____7412;
                FStar_Syntax_Syntax.lbunivs = uu____7413;
                FStar_Syntax_Syntax.lbtyp = uu____7414;
                FStar_Syntax_Syntax.lbeff = uu____7415;
                FStar_Syntax_Syntax.lbdef = uu____7416;
                FStar_Syntax_Syntax.lbattrs = uu____7417;
                FStar_Syntax_Syntax.lbpos = uu____7418;_}::uu____7419),uu____7420)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____7445),uu____7446) ->
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
          let uu____7477 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____7516))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____7556 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____7477 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____7587 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____7587 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____7591 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____7591)
                 in
              let uu____7592 = FStar_TypeChecker_Env.clear_expected_typ env
                 in
              (match uu____7592 with
               | (env',uu____7606) ->
                   let uu____7611 = tc_term env' typ  in
                   (match uu____7611 with
                    | (typ1,uu____7625,g1) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                         (let uu____7628 = tc_tactic env' tau  in
                          match uu____7628 with
                          | (tau1,uu____7642,g2) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env'
                                 g2;
                               (let t =
                                  if env.FStar_TypeChecker_Env.nosynth
                                  then
                                    let uu____7650 =
                                      let uu____7655 =
                                        FStar_TypeChecker_Util.fvar_const env
                                          FStar_Parser_Const.magic_lid
                                         in
                                      let uu____7656 =
                                        let uu____7657 =
                                          FStar_Syntax_Syntax.as_arg
                                            FStar_Syntax_Util.exp_unit
                                           in
                                        [uu____7657]  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____7655 uu____7656
                                       in
                                    uu____7650 FStar_Pervasives_Native.None
                                      rng
                                  else
                                    (let t =
                                       env.FStar_TypeChecker_Env.synth_hook
                                         env' typ1
                                         (let uu___339_7687 = tau1  in
                                          {
                                            FStar_Syntax_Syntax.n =
                                              (uu___339_7687.FStar_Syntax_Syntax.n);
                                            FStar_Syntax_Syntax.pos = rng;
                                            FStar_Syntax_Syntax.vars =
                                              (uu___339_7687.FStar_Syntax_Syntax.vars)
                                          })
                                        in
                                     (let uu____7689 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Tac")
                                         in
                                      if uu____7689
                                      then
                                        let uu____7690 =
                                          FStar_Syntax_Print.term_to_string t
                                           in
                                        FStar_Util.print1 "Got %s\n"
                                          uu____7690
                                      else ());
                                     t)
                                   in
                                FStar_TypeChecker_Util.check_uvars
                                  tau1.FStar_Syntax_Syntax.pos t;
                                (let uu____7693 =
                                   let uu____7694 =
                                     FStar_Syntax_Syntax.mk_Total typ1  in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.lcomp_of_comp
                                     uu____7694
                                    in
                                 (t, uu____7693,
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
        let uu___340_7698 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___340_7698.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___340_7698.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___340_7698.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___340_7698.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___340_7698.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___340_7698.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___340_7698.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___340_7698.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___340_7698.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___340_7698.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___340_7698.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___340_7698.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___340_7698.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___340_7698.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___340_7698.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___340_7698.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___340_7698.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___340_7698.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___340_7698.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___340_7698.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___340_7698.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___340_7698.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___340_7698.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___340_7698.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___340_7698.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___340_7698.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___340_7698.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___340_7698.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___340_7698.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___340_7698.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___340_7698.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___340_7698.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___340_7698.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___340_7698.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___340_7698.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___340_7698.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___340_7698.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___340_7698.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___340_7698.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___340_7698.FStar_TypeChecker_Env.dep_graph)
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
        let uu___341_7702 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___341_7702.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___341_7702.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___341_7702.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___341_7702.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___341_7702.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___341_7702.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___341_7702.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___341_7702.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___341_7702.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___341_7702.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___341_7702.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___341_7702.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___341_7702.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___341_7702.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___341_7702.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___341_7702.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___341_7702.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___341_7702.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___341_7702.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___341_7702.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___341_7702.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___341_7702.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___341_7702.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___341_7702.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___341_7702.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___341_7702.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___341_7702.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___341_7702.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___341_7702.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___341_7702.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___341_7702.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___341_7702.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___341_7702.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___341_7702.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___341_7702.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___341_7702.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___341_7702.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___341_7702.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___341_7702.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___341_7702.FStar_TypeChecker_Env.dep_graph)
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
          let uu____7718 = tc_tactic env tactic  in
          (match uu____7718 with
           | (tactic1,uu____7728,uu____7729) ->
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
        let uu____7778 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____7778 with
        | (e2,t,implicits) ->
            let tc =
              let uu____7799 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____7799
              then FStar_Util.Inl t
              else
                (let uu____7805 =
                   let uu____7806 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____7806
                    in
                 FStar_Util.Inr uu____7805)
               in
            let is_data_ctor uu___329_7814 =
              match uu___329_7814 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____7817) -> true
              | uu____7824 -> false  in
            let uu____7827 =
              (is_data_ctor dc) &&
                (let uu____7829 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____7829)
               in
            if uu____7827
            then
              let uu____7836 =
                let uu____7841 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____7841)  in
              let uu____7842 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____7836 uu____7842
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____7859 =
            let uu____7860 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____7860
             in
          failwith uu____7859
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____7885 =
            let uu____7890 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____7890  in
          value_check_expected_typ env1 e uu____7885
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____7892 =
            let uu____7905 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____7905 with
            | FStar_Pervasives_Native.None  ->
                let uu____7920 = FStar_Syntax_Util.type_u ()  in
                (match uu____7920 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____7892 with
           | (t,uu____7957,g0) ->
               let uu____7971 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____7971 with
                | (e1,uu____7991,g1) ->
                    let uu____8005 =
                      let uu____8006 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____8006
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____8007 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____8005, uu____8007)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____8009 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____8018 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____8018)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____8009 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___342_8031 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___342_8031.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___342_8031.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____8034 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____8034 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____8055 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____8055
                       then FStar_Util.Inl t1
                       else
                         (let uu____8061 =
                            let uu____8062 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____8062
                             in
                          FStar_Util.Inr uu____8061)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8064;
             FStar_Syntax_Syntax.vars = uu____8065;_},uu____8066)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8071 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8071
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____8079 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____8079
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____8087;
             FStar_Syntax_Syntax.vars = uu____8088;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____8097 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8097 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____8120 =
                     let uu____8125 =
                       let uu____8126 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____8127 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____8128 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____8126 uu____8127 uu____8128
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____8125)
                      in
                   let uu____8129 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____8120 uu____8129)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____8145 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8149 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8149 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8151 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8151 with
           | ((us,t),range) ->
               ((let uu____8174 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____8174
                 then
                   let uu____8175 =
                     let uu____8176 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____8176  in
                   let uu____8177 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____8178 = FStar_Range.string_of_range range  in
                   let uu____8179 = FStar_Range.string_of_use_range range  in
                   let uu____8180 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____8175 uu____8177 uu____8178 uu____8179 uu____8180
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____8185 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____8185 us  in
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
          let uu____8213 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8213 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____8227 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8227 with
                | (env2,uu____8241) ->
                    let uu____8246 = tc_binders env2 bs1  in
                    (match uu____8246 with
                     | (bs2,env3,g,us) ->
                         let uu____8265 = tc_comp env3 c1  in
                         (match uu____8265 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___343_8284 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___343_8284.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___343_8284.FStar_Syntax_Syntax.vars)
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
                                  let uu____8295 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____8295
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
          let uu____8311 =
            let uu____8316 =
              let uu____8317 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8317]  in
            FStar_Syntax_Subst.open_term uu____8316 phi  in
          (match uu____8311 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____8345 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____8345 with
                | (env2,uu____8359) ->
                    let uu____8364 =
                      let uu____8379 = FStar_List.hd x1  in
                      tc_binder env2 uu____8379  in
                    (match uu____8364 with
                     | (x2,env3,f1,u) ->
                         ((let uu____8415 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____8415
                           then
                             let uu____8416 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____8417 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____8418 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____8416 uu____8417 uu____8418
                           else ());
                          (let uu____8422 = FStar_Syntax_Util.type_u ()  in
                           match uu____8422 with
                           | (t_phi,uu____8434) ->
                               let uu____8435 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____8435 with
                                | (phi2,uu____8449,f2) ->
                                    let e1 =
                                      let uu___344_8454 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___344_8454.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___344_8454.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____8463 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____8463
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____8491) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____8518 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____8518
            then
              let uu____8519 =
                FStar_Syntax_Print.term_to_string
                  (let uu___345_8522 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___345_8522.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___345_8522.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____8519
            else ());
           (let uu____8536 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____8536 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____8549 ->
          let uu____8550 =
            let uu____8551 = FStar_Syntax_Print.term_to_string top  in
            let uu____8552 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____8551
              uu____8552
             in
          failwith uu____8550

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____8562 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____8563,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____8574,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____8590 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____8595 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____8596 ->
            let uu____8598 =
              let uu____8603 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____8603 FStar_Util.must  in
            FStar_All.pipe_right uu____8598 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____8628 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____8629 =
              let uu____8634 =
                let uu____8635 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8635
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8634)  in
            FStar_Errors.raise_error uu____8629 r
        | FStar_Const.Const_set_range_of  ->
            let uu____8636 =
              let uu____8641 =
                let uu____8642 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8642
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8641)  in
            FStar_Errors.raise_error uu____8636 r
        | FStar_Const.Const_reify  ->
            let uu____8643 =
              let uu____8648 =
                let uu____8649 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8649
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8648)  in
            FStar_Errors.raise_error uu____8643 r
        | FStar_Const.Const_reflect uu____8650 ->
            let uu____8651 =
              let uu____8656 =
                let uu____8657 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____8657
                 in
              (FStar_Errors.Fatal_IllTyped, uu____8656)  in
            FStar_Errors.raise_error uu____8651 r
        | uu____8658 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____8675) ->
          let uu____8684 = FStar_Syntax_Util.type_u ()  in
          (match uu____8684 with
           | (k,u) ->
               let uu____8697 = tc_check_tot_or_gtot_term env t k  in
               (match uu____8697 with
                | (t1,uu____8711,g) ->
                    let uu____8713 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____8713, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____8715) ->
          let uu____8724 = FStar_Syntax_Util.type_u ()  in
          (match uu____8724 with
           | (k,u) ->
               let uu____8737 = tc_check_tot_or_gtot_term env t k  in
               (match uu____8737 with
                | (t1,uu____8751,g) ->
                    let uu____8753 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____8753, u, g)))
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
            let uu____8763 =
              let uu____8768 =
                let uu____8769 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____8769 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____8768  in
            uu____8763 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____8788 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____8788 with
           | (tc1,uu____8802,f) ->
               let uu____8804 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____8804 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____8854 =
                        let uu____8855 = FStar_Syntax_Subst.compress head3
                           in
                        uu____8855.FStar_Syntax_Syntax.n  in
                      match uu____8854 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____8858,us) -> us
                      | uu____8864 -> []  in
                    let uu____8865 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____8865 with
                     | (uu____8888,args1) ->
                         let uu____8914 =
                           let uu____8937 = FStar_List.hd args1  in
                           let uu____8954 = FStar_List.tl args1  in
                           (uu____8937, uu____8954)  in
                         (match uu____8914 with
                          | (res,args2) ->
                              let uu____9035 =
                                let uu____9044 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___330_9072  ->
                                          match uu___330_9072 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____9080 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____9080 with
                                               | (env1,uu____9092) ->
                                                   let uu____9097 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____9097 with
                                                    | (e1,uu____9109,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____9044
                                  FStar_List.unzip
                                 in
                              (match uu____9035 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___346_9150 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___346_9150.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___346_9150.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____9156 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____9156 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____9160 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____9160))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____9170 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____9171 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____9181 = aux u3  in FStar_Syntax_Syntax.U_succ uu____9181
        | FStar_Syntax_Syntax.U_max us ->
            let uu____9185 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____9185
        | FStar_Syntax_Syntax.U_name x ->
            let uu____9189 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____9189
            then u2
            else
              (let uu____9191 =
                 let uu____9192 =
                   let uu____9193 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____9193 " not found"  in
                 Prims.strcat "Universe variable " uu____9192  in
               failwith uu____9191)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____9195 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____9195 FStar_Pervasives_Native.snd
         | uu____9204 -> aux u)

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
            let uu____9233 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____9233 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____9359 bs2 bs_expected1 =
              match uu____9359 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____9653)) ->
                             let uu____9658 =
                               let uu____9663 =
                                 let uu____9664 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9664
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9663)
                                in
                             let uu____9665 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9658 uu____9665
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____9666),FStar_Pervasives_Native.None ) ->
                             let uu____9671 =
                               let uu____9676 =
                                 let uu____9677 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____9677
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____9676)
                                in
                             let uu____9678 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____9671 uu____9678
                         | uu____9679 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____9689 =
                           let uu____9696 =
                             let uu____9697 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____9697.FStar_Syntax_Syntax.n  in
                           match uu____9696 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____9708 ->
                               ((let uu____9710 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____9710
                                 then
                                   let uu____9711 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____9711
                                 else ());
                                (let uu____9713 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____9713 with
                                 | (t,uu____9727,g1) ->
                                     let g2 =
                                       let uu____9730 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____9730
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____9732 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____9732 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____9735 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____9740 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____9735 uu____9740
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____9742 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____9742
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____9744 =
                                         FStar_TypeChecker_Env.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Env.conj_guard g
                                         uu____9744
                                        in
                                     (t, g3)))
                            in
                         match uu____9689 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___347_9796 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___347_9796.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___347_9796.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____9819 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____9819
                                in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         g, subst1))
               in
            aux (env1, [], FStar_TypeChecker_Env.trivial_guard, []) bs1
              bs_expected
             in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____10127 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____10136 = tc_binders env1 bs  in
                  match uu____10136 with
                  | (bs1,envbody,g,uu____10166) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____10220 =
                    let uu____10221 = FStar_Syntax_Subst.compress t2  in
                    uu____10221.FStar_Syntax_Syntax.n  in
                  match uu____10220 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____10254 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10274 -> failwith "Impossible");
                       (let uu____10283 = tc_binders env1 bs  in
                        match uu____10283 with
                        | (bs1,envbody,g,uu____10325) ->
                            let uu____10326 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10326 with
                             | (envbody1,uu____10364) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____10385;
                         FStar_Syntax_Syntax.pos = uu____10386;
                         FStar_Syntax_Syntax.vars = uu____10387;_},uu____10388)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____10432 -> failwith "Impossible");
                       (let uu____10441 = tc_binders env1 bs  in
                        match uu____10441 with
                        | (bs1,envbody,g,uu____10483) ->
                            let uu____10484 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____10484 with
                             | (envbody1,uu____10522) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____10544) ->
                      let uu____10549 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____10549 with
                       | (uu____10610,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____10687 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____10687 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____10832 c_expected2
                               body3 =
                               match uu____10832 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____10946 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____10946,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____10963 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____10963
                                           in
                                        let uu____10964 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____10964,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____10981 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____10981
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env3
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____11045 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____11045 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____11072 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____11072 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____11126 =
                                                           let uu____11153 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____11153,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____11126
                                                           c_expected4 body3))
                                           | uu____11176 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env3, bs2, guard, c, body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None
                                              in
                                           (env3, bs2, guard, c, body4)))
                                in
                             let uu____11204 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____11204 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___348_11267 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___348_11267.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___348_11267.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___348_11267.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___348_11267.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___348_11267.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___348_11267.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___348_11267.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___348_11267.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___348_11267.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___348_11267.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___348_11267.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___348_11267.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___348_11267.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___348_11267.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___348_11267.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___348_11267.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___348_11267.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___348_11267.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___348_11267.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___348_11267.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___348_11267.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___348_11267.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___348_11267.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___348_11267.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___348_11267.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___348_11267.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___348_11267.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___348_11267.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___348_11267.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___348_11267.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___348_11267.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___348_11267.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___348_11267.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___348_11267.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___348_11267.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___348_11267.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___348_11267.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___348_11267.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___348_11267.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___348_11267.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____11325  ->
                                     fun uu____11326  ->
                                       match (uu____11325, uu____11326) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____11408 =
                                             let uu____11415 =
                                               let uu____11416 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11416
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____11415 t3  in
                                           (match uu____11408 with
                                            | (t4,uu____11438,uu____11439) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____11451 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___349_11454
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___349_11454.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___349_11454.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____11451 ::
                                                        letrec_binders
                                                  | uu____11455 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____11464 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____11464 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____11540 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____11540 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g))))
                  | uu____11600 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____11631 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____11631
                      else
                        (let uu____11633 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____11633 with
                         | (uu____11682,bs1,uu____11684,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____11714 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____11714 with
          | (env1,topt) ->
              ((let uu____11734 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____11734
                then
                  let uu____11735 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____11735
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____11739 = expected_function_typ1 env1 topt body  in
                match uu____11739 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let envbody1 =
                      FStar_TypeChecker_Env.set_range envbody
                        body1.FStar_Syntax_Syntax.pos
                       in
                    let uu____11780 =
                      let should_check_expected_effect =
                        let uu____11792 =
                          let uu____11799 =
                            let uu____11800 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____11800.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____11799)  in
                        match uu____11792 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____11805,(FStar_Util.Inr
                                         expected_c,uu____11807),uu____11808))
                            -> false
                        | uu____11857 -> true  in
                      let uu____11864 =
                        tc_term
                          (let uu___350_11873 = envbody1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___350_11873.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___350_11873.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___350_11873.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___350_11873.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___350_11873.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___350_11873.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___350_11873.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___350_11873.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___350_11873.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___350_11873.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___350_11873.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___350_11873.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___350_11873.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___350_11873.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___350_11873.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___350_11873.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___350_11873.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___350_11873.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___350_11873.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___350_11873.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___350_11873.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___350_11873.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___350_11873.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___350_11873.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___350_11873.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___350_11873.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___350_11873.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___350_11873.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___350_11873.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___350_11873.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___350_11873.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___350_11873.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___350_11873.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___350_11873.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___350_11873.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___350_11873.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___350_11873.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___350_11873.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___350_11873.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____11864 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody1 guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____11898 =
                              let uu____11905 =
                                let uu____11910 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody  in
                                (body2, uu____11910)  in
                              check_expected_effect
                                (let uu___351_11913 = envbody1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___351_11913.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___351_11913.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___351_11913.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___351_11913.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___351_11913.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___351_11913.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___351_11913.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___351_11913.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___351_11913.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___351_11913.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___351_11913.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___351_11913.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___351_11913.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___351_11913.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___351_11913.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___351_11913.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___351_11913.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___351_11913.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___351_11913.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___351_11913.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___351_11913.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___351_11913.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___351_11913.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___351_11913.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___351_11913.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___351_11913.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___351_11913.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___351_11913.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___351_11913.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___351_11913.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___351_11913.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___351_11913.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___351_11913.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___351_11913.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___351_11913.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___351_11913.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___351_11913.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___351_11913.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___351_11913.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___351_11913.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____11905
                               in
                            (match uu____11898 with
                             | (body3,cbody1,guard) ->
                                 let uu____11927 =
                                   FStar_TypeChecker_Env.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____11927))
                          else
                            (let uu____11933 =
                               FStar_Syntax_Syntax.lcomp_comp cbody  in
                             (body2, uu____11933, guard_body1))
                       in
                    (match uu____11780 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____11958 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____11960 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____11960)
                              in
                           if uu____11958
                           then
                             let uu____11961 =
                               FStar_TypeChecker_Env.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody1
                               uu____11961
                           else
                             (let guard1 =
                                let uu____11964 =
                                  FStar_TypeChecker_Env.conj_guard g guard
                                   in
                                FStar_TypeChecker_Env.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____11964
                                 in
                              guard1)
                            in
                         let guard2 =
                           FStar_TypeChecker_Util.close_guard_implicits env1
                             bs1 guard1
                            in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody  in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt)))
                            in
                         let uu____11978 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____11999 ->
                                    (e, t1, guard2)
                                | uu____12014 ->
                                    let uu____12015 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____12015 with
                                     | (e1,guard') ->
                                         let uu____12028 =
                                           FStar_TypeChecker_Env.conj_guard
                                             guard2 guard'
                                            in
                                         (e1, t1, uu____12028)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard2)
                            in
                         (match uu____11978 with
                          | (e1,tfun,guard3) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun  in
                              let uu____12039 =
                                let uu____12044 =
                                  FStar_Syntax_Util.lcomp_of_comp c  in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____12044 guard3
                                 in
                              (match uu____12039 with
                               | (c1,g1) -> (e1, c1, g1))))))

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
              (let uu____12092 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____12092
               then
                 let uu____12093 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____12094 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____12093
                   uu____12094
               else ());
              (let monadic_application uu____12171 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____12171 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____12238 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____12238 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___352_12252 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___352_12252.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___352_12252.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___352_12252.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____12253 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____12269 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____12269
                                   in
                                (cres1, g)
                            | uu____12270 ->
                                let g =
                                  let uu____12280 =
                                    let uu____12281 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____12281
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____12280
                                   in
                                let uu____12282 =
                                  let uu____12283 =
                                    let uu____12284 =
                                      let uu____12285 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____12285
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____12284
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____12283
                                   in
                                (uu____12282, g)
                             in
                          (match uu____12253 with
                           | (cres2,guard1) ->
                               ((let uu____12297 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____12297
                                 then
                                   let uu____12298 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____12298
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____12314  ->
                                             match uu____12314 with
                                             | (uu____12323,uu____12324,lc)
                                                 ->
                                                 (let uu____12332 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____12332)
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
                                   let uu____12344 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____12344
                                   then
                                     ((let uu____12346 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12346
                                       then
                                         let uu____12347 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____12347
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____12351 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____12351
                                       then
                                         let uu____12352 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____12352
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____12380  ->
                                          match uu____12380 with
                                          | ((e,q),x,c) ->
                                              ((let uu____12422 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12422
                                                then
                                                  let uu____12423 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____12425 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12426 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____12423 uu____12425
                                                    uu____12426
                                                else ());
                                               (let uu____12428 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12428
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
                                   (let uu____12436 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____12436
                                    then
                                      let uu____12437 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____12437
                                    else ());
                                   (let uu____12439 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____12439
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
                                   let uu____12447 =
                                     let uu____12448 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____12448.FStar_Syntax_Syntax.n  in
                                   match uu____12447 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____12452 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____12473  ->
                                              match uu____12473 with
                                              | (arg,uu____12487,uu____12488)
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
                                     (let uu____12498 =
                                        let map_fun uu____12560 =
                                          match uu____12560 with
                                          | ((e,q),uu____12597,c) ->
                                              ((let uu____12614 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____12614
                                                then
                                                  let uu____12615 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____12616 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____12615 uu____12616
                                                else ());
                                               (let uu____12618 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____12618
                                                then
                                                  ((let uu____12640 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____12640
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  ((let uu____12670 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____12670
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
                                                    let uu____12674 =
                                                      let uu____12681 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____12681, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____12674)))))
                                           in
                                        let uu____12708 =
                                          let uu____12737 =
                                            let uu____12764 =
                                              let uu____12775 =
                                                let uu____12784 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____12784,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____12775 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____12764
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____12737
                                           in
                                        match uu____12708 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____12973 =
                                              let uu____12974 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____12974
                                               in
                                            let uu____12989 =
                                              let uu____12990 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____12990  in
                                            (lifted_args, uu____12973,
                                              uu____12989)
                                         in
                                      match uu____12498 with
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
                                            uu___331_13095 =
                                            match uu___331_13095 with
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
                                                  let uu____13156 =
                                                    let uu____13163 =
                                                      let uu____13164 =
                                                        let uu____13177 =
                                                          let uu____13180 =
                                                            let uu____13181 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____13181]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____13180 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____13177)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____13164
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____13163
                                                     in
                                                  uu____13156
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
                                 let uu____13233 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____13233 with
                                 | (comp3,g) ->
                                     ((let uu____13250 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____13250
                                       then
                                         let uu____13251 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____13252 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____13251 uu____13252
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____13330 bs args1 =
                 match uu____13330 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____13469))::rest,
                         (uu____13471,FStar_Pervasives_Native.None )::uu____13472)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____13532 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____13532 with
                           | (t1,g_ex) ->
                               let uu____13545 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____13545 with
                                | (varg,uu____13565,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____13593 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____13593)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____13601 =
                                      let uu____13636 =
                                        let uu____13647 =
                                          let uu____13656 =
                                            let uu____13657 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____13657
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____13656)
                                           in
                                        uu____13647 :: outargs  in
                                      (subst2, uu____13636, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____13601 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____13703,FStar_Pervasives_Native.None
                                                                 )::uu____13704)
                          ->
                          let uu____13765 = tc_tactic env tau  in
                          (match uu____13765 with
                           | (tau1,uu____13779,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____13782 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____13782 with
                                | (t1,g_ex) ->
                                    let uu____13795 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                       in
                                    (match uu____13795 with
                                     | (varg,uu____13815,implicits) ->
                                         let mark_meta_implicits tau2 g1 =
                                           let uu___353_13840 = g1  in
                                           let uu____13841 =
                                             FStar_List.map
                                               (fun imp  ->
                                                  let uu___354_13847 = imp
                                                     in
                                                  {
                                                    FStar_TypeChecker_Env.imp_reason
                                                      =
                                                      (uu___354_13847.FStar_TypeChecker_Env.imp_reason);
                                                    FStar_TypeChecker_Env.imp_uvar
                                                      =
                                                      (uu___354_13847.FStar_TypeChecker_Env.imp_uvar);
                                                    FStar_TypeChecker_Env.imp_tm
                                                      =
                                                      (uu___354_13847.FStar_TypeChecker_Env.imp_tm);
                                                    FStar_TypeChecker_Env.imp_range
                                                      =
                                                      (uu___354_13847.FStar_TypeChecker_Env.imp_range);
                                                    FStar_TypeChecker_Env.imp_meta
                                                      =
                                                      (FStar_Pervasives_Native.Some
                                                         (env, tau2))
                                                  })
                                               g1.FStar_TypeChecker_Env.implicits
                                              in
                                           {
                                             FStar_TypeChecker_Env.guard_f =
                                               (uu___353_13840.FStar_TypeChecker_Env.guard_f);
                                             FStar_TypeChecker_Env.deferred =
                                               (uu___353_13840.FStar_TypeChecker_Env.deferred);
                                             FStar_TypeChecker_Env.univ_ineqs
                                               =
                                               (uu___353_13840.FStar_TypeChecker_Env.univ_ineqs);
                                             FStar_TypeChecker_Env.implicits
                                               = uu____13841
                                           }  in
                                         let implicits1 =
                                           mark_meta_implicits tau1 implicits
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____13867 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____13867)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits1
                                            in
                                         let uu____13875 =
                                           let uu____13910 =
                                             let uu____13921 =
                                               let uu____13930 =
                                                 let uu____13931 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____13931
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____13930)
                                                in
                                             uu____13921 :: outargs  in
                                           (subst2, uu____13910, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____13875 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____14047,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____14048)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____14057),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14058)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____14065),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14066)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____14079 ->
                                let uu____14088 =
                                  let uu____14093 =
                                    let uu____14094 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____14095 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____14096 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____14097 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____14094 uu____14095 uu____14096
                                      uu____14097
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____14093)
                                   in
                                FStar_Errors.raise_error uu____14088
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___355_14100 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___355_14100.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___355_14100.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____14102 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____14102
                             then
                               let uu____14103 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____14104 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____14105 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14106 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____14107 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____14103 uu____14104 uu____14105
                                 uu____14106 uu____14107
                             else ());
                            (let uu____14109 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____14109 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___356_14124 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___356_14124.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___356_14124.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___356_14124.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___356_14124.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___356_14124.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___356_14124.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___356_14124.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___356_14124.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___356_14124.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___356_14124.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___356_14124.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___356_14124.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___356_14124.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___356_14124.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___356_14124.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___356_14124.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___356_14124.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___356_14124.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___356_14124.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___356_14124.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___356_14124.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___356_14124.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___356_14124.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___356_14124.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___356_14124.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___356_14124.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___356_14124.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___356_14124.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___356_14124.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___356_14124.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___356_14124.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___356_14124.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___356_14124.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___356_14124.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___356_14124.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___356_14124.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___356_14124.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___356_14124.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___356_14124.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___356_14124.FStar_TypeChecker_Env.dep_graph)
                                   }  in
                                 ((let uu____14126 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____14126
                                   then
                                     let uu____14127 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____14128 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____14129 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____14127 uu____14128 uu____14129
                                   else ());
                                  (let uu____14131 = tc_term env2 e  in
                                   match uu____14131 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____14148 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____14148
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____14171 =
                                           let uu____14174 =
                                             let uu____14183 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14183
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____14174
                                            in
                                         (uu____14171, aq)  in
                                       let uu____14192 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____14192
                                       then
                                         let subst2 =
                                           let uu____14200 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____14200 e1
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
                      | (uu____14298,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____14334) ->
                          let uu____14385 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____14385 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____14437 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____14437
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____14468 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____14468 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____14490 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____14490)
                                             in
                                          ((let uu____14492 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____14492
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
                                 | uu____14534 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____14542 =
                                         let uu____14543 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____14543.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14542 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____14546;
                                              FStar_Syntax_Syntax.index =
                                                uu____14547;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____14549)
                                           -> norm_tres tres4
                                       | uu____14556 -> tres3  in
                                     let uu____14557 = norm_tres tres1  in
                                     aux true solve ghead2 uu____14557
                                 | uu____14558 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____14560 ->
                                     let uu____14561 =
                                       let uu____14566 =
                                         let uu____14567 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____14568 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____14575 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____14567 uu____14568
                                           uu____14575
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____14566)
                                        in
                                     let uu____14576 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____14561
                                       uu____14576
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____14604 =
                   let uu____14605 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____14605.FStar_Syntax_Syntax.n  in
                 match uu____14604 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____14614 ->
                     let uu____14627 =
                       FStar_List.fold_right
                         (fun uu____14658  ->
                            fun uu____14659  ->
                              match uu____14659 with
                              | (bs,guard1) ->
                                  let uu____14686 =
                                    let uu____14699 =
                                      let uu____14700 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____14700
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____14699
                                     in
                                  (match uu____14686 with
                                   | (t,uu____14716,g) ->
                                       let uu____14730 =
                                         let uu____14733 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____14733 :: bs  in
                                       let uu____14734 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____14730, uu____14734))) args
                         ([], guard)
                        in
                     (match uu____14627 with
                      | (bs,guard1) ->
                          let uu____14751 =
                            let uu____14758 =
                              let uu____14771 =
                                let uu____14772 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____14772
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____14771
                               in
                            match uu____14758 with
                            | (t,uu____14788,g) ->
                                let uu____14802 = FStar_Options.ml_ish ()  in
                                if uu____14802
                                then
                                  let uu____14809 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____14812 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____14809, uu____14812)
                                else
                                  (let uu____14816 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____14819 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____14816, uu____14819))
                             in
                          (match uu____14751 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____14838 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____14838
                                 then
                                   let uu____14839 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____14840 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____14841 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____14839 uu____14840 uu____14841
                                 else ());
                                (let g =
                                   let uu____14844 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____14844
                                    in
                                 let uu____14845 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____14845))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____14846;
                        FStar_Syntax_Syntax.pos = uu____14847;
                        FStar_Syntax_Syntax.vars = uu____14848;_},uu____14849)
                     ->
                     let uu____14886 =
                       FStar_List.fold_right
                         (fun uu____14917  ->
                            fun uu____14918  ->
                              match uu____14918 with
                              | (bs,guard1) ->
                                  let uu____14945 =
                                    let uu____14958 =
                                      let uu____14959 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____14959
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____14958
                                     in
                                  (match uu____14945 with
                                   | (t,uu____14975,g) ->
                                       let uu____14989 =
                                         let uu____14992 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____14992 :: bs  in
                                       let uu____14993 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____14989, uu____14993))) args
                         ([], guard)
                        in
                     (match uu____14886 with
                      | (bs,guard1) ->
                          let uu____15010 =
                            let uu____15017 =
                              let uu____15030 =
                                let uu____15031 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____15031
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____15030
                               in
                            match uu____15017 with
                            | (t,uu____15047,g) ->
                                let uu____15061 = FStar_Options.ml_ish ()  in
                                if uu____15061
                                then
                                  let uu____15068 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____15071 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____15068, uu____15071)
                                else
                                  (let uu____15075 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____15078 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____15075, uu____15078))
                             in
                          (match uu____15010 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____15097 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____15097
                                 then
                                   let uu____15098 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____15099 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____15100 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____15098 uu____15099 uu____15100
                                 else ());
                                (let g =
                                   let uu____15103 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____15103
                                    in
                                 let uu____15104 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____15104))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____15127 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____15127 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____15149 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____15149)  in
                          tc_args head_info ([], [], [], guard, []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____15191) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____15197,uu____15198) ->
                     check_function_app t guard
                 | uu____15239 ->
                     let uu____15240 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____15240
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
                  let uu____15322 =
                    FStar_List.fold_left2
                      (fun uu____15389  ->
                         fun uu____15390  ->
                           fun uu____15391  ->
                             match (uu____15389, uu____15390, uu____15391)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____15541 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____15541 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____15569 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____15569 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____15573 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____15573)
                                              &&
                                              (let uu____15575 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____15575))
                                          in
                                       let uu____15576 =
                                         let uu____15587 =
                                           let uu____15598 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____15598]  in
                                         FStar_List.append seen uu____15587
                                          in
                                       let uu____15631 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____15576, uu____15631, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____15322 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____15693 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____15693
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____15695 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____15695 with | (c2,g) -> (e, c2, g)))
              | uu____15711 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

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
        let uu____15754 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____15754 with
        | (pattern,when_clause,branch_exp) ->
            let uu____15799 = branch1  in
            (match uu____15799 with
             | (cpat,uu____15840,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____15917 = FStar_Syntax_Util.type_u ()  in
                     match uu____15917 with
                     | (tu,u) ->
                         let uu____15928 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____15928 with
                          | (t1,uu____15940,g) -> (t1, g))
                      in
                   let uu____15942 =
                     FStar_TypeChecker_PatternUtils.pat_as_exp
                       allow_implicits env p0 tc_annot
                      in
                   match uu____15942 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____15976 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____15976
                         then
                           ((let uu____15978 =
                               FStar_Syntax_Print.pat_to_string p0  in
                             let uu____15979 =
                               FStar_Syntax_Print.pat_to_string p  in
                             FStar_Util.print2
                               "Pattern %s elaborated to %s\n" uu____15978
                               uu____15979);
                            (let uu____15980 =
                               FStar_Syntax_Print.bvs_to_string ", " pat_bvs1
                                in
                             FStar_Util.print1 "pat_bvs = [%s]\n" uu____15980))
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____15983 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____15983 with
                         | (env1,uu____16005) ->
                             let env11 =
                               let uu___357_16011 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___357_16011.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___357_16011.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___357_16011.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___357_16011.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___357_16011.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___357_16011.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___357_16011.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___357_16011.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___357_16011.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___357_16011.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___357_16011.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___357_16011.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___357_16011.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___357_16011.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___357_16011.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___357_16011.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___357_16011.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___357_16011.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___357_16011.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___357_16011.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___357_16011.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___357_16011.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___357_16011.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___357_16011.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___357_16011.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___357_16011.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___357_16011.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___357_16011.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___357_16011.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___357_16011.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___357_16011.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___357_16011.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___357_16011.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___357_16011.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___357_16011.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___357_16011.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___357_16011.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___357_16011.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___357_16011.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___357_16011.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____16014 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____16014
                               then
                                 let uu____16015 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____16016 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____16015 uu____16016
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____16019 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____16019 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___358_16044 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___358_16044.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___358_16044.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___358_16044.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____16045 =
                                     let uu____16046 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____16046
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____16048 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____16048
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env13)
                                     else
                                       (let uu____16050 =
                                          let uu____16055 =
                                            let uu____16056 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____16057 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____16056 uu____16057
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____16055)
                                           in
                                        FStar_Errors.raise_error uu____16050
                                          exp1.FStar_Syntax_Syntax.pos)
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs_to_string uvs =
                                     let uu____16069 =
                                       let uu____16072 =
                                         FStar_Util.set_elements uvs  in
                                       FStar_All.pipe_right uu____16072
                                         (FStar_List.map
                                            (fun u  ->
                                               FStar_Syntax_Print.uvar_to_string
                                                 u.FStar_Syntax_Syntax.ctx_uvar_head))
                                        in
                                     FStar_All.pipe_right uu____16069
                                       (FStar_String.concat ", ")
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____16090 =
                                       FStar_TypeChecker_Env.debug env
                                         (FStar_Options.Other "Free")
                                        in
                                     if uu____16090
                                     then
                                       ((let uu____16092 =
                                           FStar_Syntax_Print.term_to_string
                                             norm_exp
                                            in
                                         let uu____16093 = uvs_to_string uvs1
                                            in
                                         FStar_Util.print2
                                           ">> free_1(%s) = %s\n" uu____16092
                                           uu____16093);
                                        (let uu____16094 =
                                           FStar_Syntax_Print.term_to_string
                                             expected_pat_t
                                            in
                                         let uu____16095 = uvs_to_string uvs2
                                            in
                                         FStar_Util.print2
                                           ">> free_2(%s) = %s\n" uu____16094
                                           uu____16095))
                                     else ());
                                    (let uu____16098 =
                                       let uu____16099 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____16099
                                        in
                                     if uu____16098
                                     then
                                       let unresolved =
                                         FStar_Util.set_difference uvs1 uvs2
                                          in
                                       let uu____16103 =
                                         let uu____16108 =
                                           let uu____16109 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____16110 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____16111 =
                                             uvs_to_string unresolved  in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____16109 uu____16110
                                             uu____16111
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____16108)
                                          in
                                       FStar_Errors.raise_error uu____16103
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____16114 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____16114
                                     then
                                       let uu____16115 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____16115
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1
                                        in
                                     (p1, pat_bvs1, pat_env, exp1,
                                       guard_pat_annots, norm_exp)))))))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____16124 =
                   let uu____16131 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____16131
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____16124 with
                  | (scrutinee_env,uu____16164) ->
                      let uu____16169 = tc_pat true pat_t pattern  in
                      (match uu____16169 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____16219 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____16249 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____16249
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____16267 =
                                      let uu____16274 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____16274 e  in
                                    match uu____16267 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____16219 with
                            | (when_clause1,g_when) ->
                                let uu____16327 = tc_term pat_env branch_exp
                                   in
                                (match uu____16327 with
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
                                             let uu____16382 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_17  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_17) uu____16382
                                          in
                                       let uu____16393 =
                                         let eqs =
                                           let uu____16414 =
                                             let uu____16415 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____16415
                                              in
                                           if uu____16414
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____16428 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____16443 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____16446 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____16449 ->
                                                  let uu____16450 =
                                                    let uu____16453 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____16453 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____16450)
                                            in
                                         let uu____16456 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch1
                                            in
                                         match uu____16456 with
                                         | (c1,g_branch2) ->
                                             let uu____16481 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____16498 when
                                                   let uu____16511 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____16511
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
                                                   let uu____16541 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____16542 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____16541, uu____16542)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____16563 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____16563
                                                      in
                                                   let uu____16564 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____16565 =
                                                     let uu____16566 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____16566 g_when
                                                      in
                                                   (uu____16564, uu____16565)
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
                                                   let uu____16584 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____16584, g_when)
                                                in
                                             (match uu____16481 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return =
                                                    let c_weak1 =
                                                      let uu____16624 =
                                                        should_return &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____16624
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____16626 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____16626, g_branch2))
                                          in
                                       match uu____16393 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                           ->
                                           let branch_guard =
                                             let uu____16673 =
                                               let uu____16674 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____16674
                                                in
                                             if uu____16673
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____16716 =
                                                      let uu____16717 =
                                                        let uu____16718 =
                                                          let uu____16721 =
                                                            let uu____16728 =
                                                              FStar_TypeChecker_Env.typ_of_datacon
                                                                env
                                                                f.FStar_Syntax_Syntax.v
                                                               in
                                                            FStar_TypeChecker_Env.datacons_of_typ
                                                              env uu____16728
                                                             in
                                                          FStar_Pervasives_Native.snd
                                                            uu____16721
                                                           in
                                                        FStar_List.length
                                                          uu____16718
                                                         in
                                                      uu____16717 >
                                                        (Prims.parse_int "1")
                                                       in
                                                    if uu____16716
                                                    then
                                                      let discriminator =
                                                        FStar_Syntax_Util.mk_discriminator
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      let uu____16734 =
                                                        FStar_TypeChecker_Env.try_lookup_lid
                                                          env discriminator
                                                         in
                                                      match uu____16734 with
                                                      | FStar_Pervasives_Native.None
                                                           -> []
                                                      | uu____16755 ->
                                                          let disc =
                                                            FStar_Syntax_Syntax.fvar
                                                              discriminator
                                                              (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                 (Prims.parse_int "1"))
                                                              FStar_Pervasives_Native.None
                                                             in
                                                          let disc1 =
                                                            let uu____16770 =
                                                              let uu____16775
                                                                =
                                                                let uu____16776
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                   in
                                                                [uu____16776]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                disc
                                                                uu____16775
                                                               in
                                                            uu____16770
                                                              FStar_Pervasives_Native.None
                                                              scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                             in
                                                          let uu____16803 =
                                                            FStar_Syntax_Util.mk_eq2
                                                              FStar_Syntax_Syntax.U_zero
                                                              FStar_Syntax_Util.t_bool
                                                              disc1
                                                              FStar_Syntax_Util.exp_true_bool
                                                             in
                                                          [uu____16803]
                                                    else []  in
                                                  let fail1 uu____16810 =
                                                    let uu____16811 =
                                                      let uu____16812 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____16813 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____16814 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____16812
                                                        uu____16813
                                                        uu____16814
                                                       in
                                                    failwith uu____16811  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____16827) ->
                                                        head_constructor t1
                                                    | uu____16832 -> fail1 ()
                                                     in
                                                  let pat_exp2 =
                                                    let uu____16836 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16836
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match pat_exp2.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      uu____16841 -> []
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_uvar
                                                           uu____16854;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu____16855;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu____16856;_},uu____16857)
                                                      -> []
                                                  | FStar_Syntax_Syntax.Tm_name
                                                      uu____16894 -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      (FStar_Const.Const_unit
                                                      ) -> []
                                                  | FStar_Syntax_Syntax.Tm_constant
                                                      c1 ->
                                                      let uu____16896 =
                                                        let uu____16897 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____16897
                                                          scrutinee_tm1
                                                          pat_exp2
                                                         in
                                                      [uu____16896]
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      uu____16898 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____16906 =
                                                        let uu____16907 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16907
                                                         in
                                                      if uu____16906
                                                      then []
                                                      else
                                                        (let uu____16911 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____16911)
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      uu____16914 ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____16916 =
                                                        let uu____16917 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16917
                                                         in
                                                      if uu____16916
                                                      then []
                                                      else
                                                        (let uu____16921 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           scrutinee_tm1
                                                           uu____16921)
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,args) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____16951 =
                                                        let uu____16952 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____16952
                                                         in
                                                      if uu____16951
                                                      then []
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____16959 =
                                                             FStar_All.pipe_right
                                                               args
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____16995
                                                                     ->
                                                                    match uu____16995
                                                                    with
                                                                    | 
                                                                    (ei,uu____17007)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____17017
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____17017
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____17038
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____17052
                                                                    =
                                                                    let uu____17057
                                                                    =
                                                                    let uu____17058
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____17058
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____17059
                                                                    =
                                                                    let uu____17060
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____17060]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____17057
                                                                    uu____17059
                                                                     in
                                                                    uu____17052
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____16959
                                                             FStar_List.flatten
                                                            in
                                                         let uu____17093 =
                                                           discriminate
                                                             scrutinee_tm1 f
                                                            in
                                                         FStar_List.append
                                                           uu____17093
                                                           sub_term_guards)
                                                  | uu____17096 -> []  in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pat =
                                                  let uu____17112 =
                                                    let uu____17113 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____17113
                                                     in
                                                  if uu____17112
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____17116 =
                                                         build_branch_guard
                                                           scrutinee_tm1 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____17116
                                                        in
                                                     let uu____17125 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____17125 with
                                                     | (k,uu____17131) ->
                                                         let uu____17132 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____17132
                                                          with
                                                          | (t1,uu____17140,uu____17141)
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
                                           ((let uu____17153 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____17153
                                             then
                                               let uu____17154 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____17154
                                             else ());
                                            (let uu____17156 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____17173 =
                                               let uu____17174 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____17174 guard
                                                in
                                             (uu____17156, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____17173))))))))))

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
          let uu____17217 = check_let_bound_def true env1 lb  in
          (match uu____17217 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____17239 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____17260 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____17260, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____17265 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____17265
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____17267 =
                      let uu____17280 =
                        let uu____17295 =
                          let uu____17304 =
                            let uu____17311 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____17311)
                             in
                          [uu____17304]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____17295
                         in
                      FStar_List.hd uu____17280  in
                    match uu____17267 with
                    | (uu____17346,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Env.abstract_guard_n gvs g12  in
                        let uu____17360 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____17360))
                  in
               (match uu____17239 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____17377 =
                      let uu____17386 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____17386
                      then
                        let uu____17395 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____17395 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____17424 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____17424
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____17425 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____17425, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____17439 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____17439
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm;
                                 FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____17445 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____17445
                            then e2
                            else
                              ((let uu____17450 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____17450
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
                    (match uu____17377 with
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
                         let uu____17477 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____17488 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____17477, uu____17488,
                           FStar_TypeChecker_Env.trivial_guard))))
      | uu____17489 -> failwith "Impossible"

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
            let uu___359_17520 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___359_17520.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___359_17520.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___359_17520.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___359_17520.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___359_17520.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___359_17520.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___359_17520.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___359_17520.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___359_17520.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___359_17520.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___359_17520.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___359_17520.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___359_17520.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___359_17520.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___359_17520.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___359_17520.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___359_17520.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___359_17520.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___359_17520.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___359_17520.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___359_17520.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___359_17520.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___359_17520.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___359_17520.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___359_17520.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___359_17520.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___359_17520.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___359_17520.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___359_17520.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___359_17520.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___359_17520.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___359_17520.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___359_17520.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___359_17520.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___359_17520.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___359_17520.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___359_17520.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___359_17520.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___359_17520.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___359_17520.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____17521 =
            let uu____17532 =
              let uu____17533 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____17533 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____17532 lb  in
          (match uu____17521 with
           | (e1,uu____17555,c1,g1,annotated) ->
               ((let uu____17560 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____17564 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____17564)
                    in
                 if uu____17560
                 then
                   let uu____17565 =
                     let uu____17570 =
                       let uu____17571 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____17572 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____17571 uu____17572
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____17570)
                      in
                   FStar_Errors.raise_error uu____17565
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___360_17575 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___360_17575.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___360_17575.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____17576 =
                   let uu____17581 =
                     let uu____17582 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____17582]  in
                   FStar_Syntax_Subst.open_term uu____17581 e2  in
                 match uu____17576 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____17626 = tc_term env_x e21  in
                     (match uu____17626 with
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
                            let uu____17651 =
                              let uu____17658 =
                                let uu____17659 =
                                  let uu____17672 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____17672)  in
                                FStar_Syntax_Syntax.Tm_let uu____17659  in
                              FStar_Syntax_Syntax.mk uu____17658  in
                            uu____17651 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____17690 =
                              let uu____17691 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____17692 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____17691
                                c1.FStar_Syntax_Syntax.res_typ uu____17692
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_18  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_18)
                              uu____17690
                             in
                          let g21 =
                            let uu____17694 =
                              let uu____17695 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____17695 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____17694
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____17698 =
                            let uu____17699 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____17699  in
                          if uu____17698
                          then
                            let tt =
                              let uu____17709 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____17709
                                FStar_Option.get
                               in
                            ((let uu____17715 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____17715
                              then
                                let uu____17716 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____17717 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____17716 uu____17717
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____17720 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____17720 with
                             | (t,g_ex) ->
                                 ((let uu____17734 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____17734
                                   then
                                     let uu____17735 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____17736 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____17735 uu____17736
                                   else ());
                                  (let uu____17738 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___361_17740 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___361_17740.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___361_17740.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___361_17740.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____17738))))))))
      | uu____17741 -> failwith "Impossible"

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
          let uu____17773 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____17773 with
           | (lbs1,e21) ->
               let uu____17792 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____17792 with
                | (env0,topt) ->
                    let uu____17811 = build_let_rec_env true env0 lbs1  in
                    (match uu____17811 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____17833 = check_let_recs rec_env lbs2  in
                         (match uu____17833 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____17853 =
                                  let uu____17854 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____17854
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____17853
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____17860 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____17860
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
                                     let uu____17909 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____17943 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____17943)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____17909
                                      in
                                   FStar_List.map2
                                     (fun uu____17977  ->
                                        fun lb  ->
                                          match uu____17977 with
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
                                let uu____18025 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____18025
                                 in
                              let uu____18026 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____18026 with
                               | (lbs5,e22) ->
                                   ((let uu____18046 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____18046
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____18047 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____18047, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____18058 -> failwith "Impossible"

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
          let uu____18090 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____18090 with
           | (lbs1,e21) ->
               let uu____18109 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____18109 with
                | (env0,topt) ->
                    let uu____18128 = build_let_rec_env false env0 lbs1  in
                    (match uu____18128 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____18150 =
                           let uu____18157 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____18157
                             (fun uu____18180  ->
                                match uu____18180 with
                                | (lbs3,g) ->
                                    let uu____18199 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____18199))
                            in
                         (match uu____18150 with
                          | (lbs3,g_lbs) ->
                              let uu____18214 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___362_18237 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___362_18237.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___362_18237.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___363_18239 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___363_18239.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____18214 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____18266 = tc_term env2 e21  in
                                   (match uu____18266 with
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
                                          let uu____18285 =
                                            let uu____18286 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____18286 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____18285
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
                                          let uu___364_18296 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___364_18296.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___364_18296.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___364_18296.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____18304 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____18304))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____18305 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____18305 with
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
                                                  uu____18343 ->
                                                  (e, cres4, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____18344 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____18344 with
                                                   | (tres1,g_ex) ->
                                                       let cres5 =
                                                         let uu___365_18358 =
                                                           cres4  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___365_18358.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___365_18358.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___365_18358.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____18359 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres5,
                                                         uu____18359))))))))))
      | uu____18360 -> failwith "Impossible"

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
          let uu____18405 = FStar_Options.ml_ish ()  in
          if uu____18405
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____18408 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____18408 with
             | (formals,c) ->
                 let uu____18439 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____18439 with
                  | (actuals,uu____18449,uu____18450) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____18467 =
                          let uu____18472 =
                            let uu____18473 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____18474 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____18473 uu____18474
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____18472)
                           in
                        FStar_Errors.raise_error uu____18467
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____18477 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____18477 actuals
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
                                (let uu____18504 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____18504)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____18524 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____18524)
                               in
                            let msg =
                              let uu____18532 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____18533 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____18532 uu____18533 formals_msg
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
        let uu____18540 =
          FStar_List.fold_left
            (fun uu____18573  ->
               fun lb  ->
                 match uu____18573 with
                 | (lbs1,env1,g_acc) ->
                     let uu____18598 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____18598 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____18618 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____18635 =
                                 let uu____18642 =
                                   let uu____18643 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____18643
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___366_18654 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___366_18654.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___366_18654.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___366_18654.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___366_18654.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___366_18654.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___366_18654.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___366_18654.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___366_18654.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___366_18654.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___366_18654.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___366_18654.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___366_18654.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___366_18654.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___366_18654.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___366_18654.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___366_18654.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___366_18654.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___366_18654.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___366_18654.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___366_18654.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___366_18654.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___366_18654.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___366_18654.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___366_18654.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___366_18654.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___366_18654.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___366_18654.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___366_18654.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___366_18654.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___366_18654.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___366_18654.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___366_18654.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___366_18654.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___366_18654.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___366_18654.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___366_18654.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___366_18654.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___366_18654.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___366_18654.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___366_18654.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____18642
                                  in
                               match uu____18635 with
                               | (t1,uu____18662,g) ->
                                   let uu____18664 =
                                     let uu____18665 =
                                       let uu____18666 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____18666
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____18665
                                      in
                                   let uu____18667 = norm env01 t1  in
                                   (uu____18664, uu____18667))
                             in
                          (match uu____18618 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____18687 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____18687
                                 then
                                   let uu___367_18688 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___367_18688.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___367_18688.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___367_18688.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___367_18688.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___367_18688.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___367_18688.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___367_18688.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___367_18688.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___367_18688.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___367_18688.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___367_18688.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___367_18688.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___367_18688.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___367_18688.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___367_18688.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___367_18688.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___367_18688.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___367_18688.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___367_18688.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___367_18688.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___367_18688.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___367_18688.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___367_18688.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___367_18688.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___367_18688.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___367_18688.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___367_18688.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___367_18688.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___367_18688.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___367_18688.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___367_18688.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___367_18688.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___367_18688.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___367_18688.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___367_18688.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___367_18688.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___367_18688.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___367_18688.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___367_18688.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___367_18688.FStar_TypeChecker_Env.dep_graph)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___368_18701 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___368_18701.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___368_18701.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___368_18701.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___368_18701.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____18540 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____18727 =
        let uu____18736 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____18762 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____18762 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____18792 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____18792
                       | uu____18797 ->
                           let lb1 =
                             let uu___369_18800 = lb  in
                             let uu____18801 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____18801;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___369_18800.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____18804 =
                             let uu____18811 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____18811
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____18804 with
                            | (e,c,g) ->
                                ((let uu____18820 =
                                    let uu____18821 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____18821  in
                                  if uu____18820
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
        FStar_All.pipe_right uu____18736 FStar_List.unzip  in
      match uu____18727 with
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
        let uu____18870 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____18870 with
        | (env1,uu____18888) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____18896 = check_lbtyp top_level env lb  in
            (match uu____18896 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____18940 =
                     tc_maybe_toplevel_term
                       (let uu___370_18949 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___370_18949.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___370_18949.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___370_18949.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___370_18949.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___370_18949.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___370_18949.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___370_18949.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___370_18949.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___370_18949.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___370_18949.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___370_18949.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___370_18949.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___370_18949.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___370_18949.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___370_18949.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___370_18949.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___370_18949.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___370_18949.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___370_18949.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___370_18949.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___370_18949.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___370_18949.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___370_18949.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___370_18949.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___370_18949.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___370_18949.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___370_18949.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___370_18949.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___370_18949.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___370_18949.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___370_18949.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___370_18949.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___370_18949.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___370_18949.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___370_18949.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___370_18949.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___370_18949.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___370_18949.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___370_18949.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___370_18949.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____18940 with
                   | (e12,c1,g1) ->
                       let uu____18963 =
                         let uu____18968 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____18973  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____18968 e12 c1 wf_annot
                          in
                       (match uu____18963 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____18988 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____18988
                              then
                                let uu____18989 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____18990 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____18991 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____18989 uu____18990 uu____18991
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
            let uu____19025 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____19025 with
             | (univ_opening,univ_vars1) ->
                 let uu____19058 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____19058))
        | uu____19063 ->
            let uu____19064 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____19064 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____19113 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____19113)
                 else
                   (let uu____19119 = FStar_Syntax_Util.type_u ()  in
                    match uu____19119 with
                    | (k,uu____19139) ->
                        let uu____19140 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____19140 with
                         | (t2,uu____19162,g) ->
                             ((let uu____19165 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____19165
                               then
                                 let uu____19166 =
                                   let uu____19167 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____19167
                                    in
                                 let uu____19168 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____19166 uu____19168
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____19171 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____19171))))))

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
    fun uu____19177  ->
      match uu____19177 with
      | (x,imp) ->
          let uu____19204 = FStar_Syntax_Util.type_u ()  in
          (match uu____19204 with
           | (tu,u) ->
               ((let uu____19226 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____19226
                 then
                   let uu____19227 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____19228 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____19229 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____19227 uu____19228 uu____19229
                 else ());
                (let uu____19231 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____19231 with
                 | (t,uu____19253,g) ->
                     let x1 =
                       ((let uu___371_19265 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___371_19265.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___371_19265.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____19267 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____19267
                       then
                         let uu____19268 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____19271 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____19268 uu____19271
                       else ());
                      (let uu____19273 = push_binding env x1  in
                       (x1, uu____19273, g, u))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun bs  ->
      (let uu____19285 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____19285
       then
         let uu____19286 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____19286
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____19395 = tc_binder env1 b  in
             (match uu____19395 with
              | (b1,env',g,u) ->
                  let uu____19444 = aux env' bs2  in
                  (match uu____19444 with
                   | (bs3,env'1,g',us) ->
                       let uu____19505 =
                         let uu____19506 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____19506  in
                       ((b1 :: bs3), env'1, uu____19505, (u :: us))))
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
          (fun uu____19613  ->
             fun uu____19614  ->
               match (uu____19613, uu____19614) with
               | ((t,imp),(args1,g)) ->
                   let uu____19705 = tc_term env1 t  in
                   (match uu____19705 with
                    | (t1,uu____19725,g') ->
                        let uu____19727 =
                          FStar_TypeChecker_Env.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____19727))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____19781  ->
             match uu____19781 with
             | (pats1,g) ->
                 let uu____19808 = tc_args env p  in
                 (match uu____19808 with
                  | (args,g') ->
                      let uu____19821 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____19821))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____19834 = tc_maybe_toplevel_term env e  in
      match uu____19834 with
      | (e1,c,g) ->
          let uu____19850 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____19850
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____19861 =
               let uu____19866 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____19866
               then
                 let uu____19871 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____19871, false)
               else
                 (let uu____19873 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____19873, true))
                in
             match uu____19861 with
             | (target_comp,allow_ghost) ->
                 let uu____19882 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____19882 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____19892 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____19893 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____19892, uu____19893)
                  | uu____19894 ->
                      if allow_ghost
                      then
                        let uu____19903 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____19903
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____19915 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____19915
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
      let uu____19938 = tc_tot_or_gtot_term env t  in
      match uu____19938 with
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
      (let uu____19970 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____19970
       then
         let uu____19971 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____19971
       else ());
      (let env1 =
         let uu___372_19974 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___372_19974.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___372_19974.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___372_19974.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___372_19974.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___372_19974.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___372_19974.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___372_19974.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___372_19974.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___372_19974.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___372_19974.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___372_19974.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___372_19974.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___372_19974.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___372_19974.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___372_19974.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___372_19974.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___372_19974.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___372_19974.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___372_19974.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___372_19974.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___372_19974.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___372_19974.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___372_19974.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___372_19974.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___372_19974.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___372_19974.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___372_19974.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___372_19974.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___372_19974.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___372_19974.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___372_19974.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___372_19974.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___372_19974.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___372_19974.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___372_19974.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___372_19974.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___372_19974.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___372_19974.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___372_19974.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____19981 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____20016) ->
             let uu____20017 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____20017
          in
       match uu____19981 with
       | (t,c,g) ->
           let uu____20033 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____20033
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____20041 =
                let uu____20046 =
                  let uu____20047 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____20047
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____20046)
                 in
              let uu____20048 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____20041 uu____20048))
  
let level_of_type_fail :
  'Auu____20063 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____20063
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____20079 =
          let uu____20084 =
            let uu____20085 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____20085 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____20084)  in
        let uu____20086 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____20079 uu____20086
  
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
          let uu____20121 =
            let uu____20122 = FStar_Syntax_Util.unrefine t1  in
            uu____20122.FStar_Syntax_Syntax.n  in
          match uu____20121 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____20126 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____20129 = FStar_Syntax_Util.type_u ()  in
                 match uu____20129 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___375_20137 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___375_20137.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___375_20137.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___375_20137.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___375_20137.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___375_20137.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___375_20137.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___375_20137.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___375_20137.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___375_20137.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___375_20137.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___375_20137.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___375_20137.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___375_20137.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___375_20137.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___375_20137.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___375_20137.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___375_20137.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___375_20137.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___375_20137.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___375_20137.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___375_20137.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___375_20137.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___375_20137.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___375_20137.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___375_20137.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___375_20137.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___375_20137.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___375_20137.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___375_20137.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___375_20137.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___375_20137.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___375_20137.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___375_20137.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___375_20137.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___375_20137.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___375_20137.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___375_20137.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___375_20137.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___375_20137.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___375_20137.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____20141 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____20141
                       | uu____20142 ->
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
      let uu____20159 =
        let uu____20160 = FStar_Syntax_Subst.compress e  in
        uu____20160.FStar_Syntax_Syntax.n  in
      match uu____20159 with
      | FStar_Syntax_Syntax.Tm_bvar uu____20165 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____20170 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____20195 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____20211) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____20257) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____20264 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20264 with | ((uu____20275,t),uu____20277) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____20283 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____20283
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20286,(FStar_Util.Inl t,uu____20288),uu____20289) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20336,(FStar_Util.Inr c,uu____20338),uu____20339) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____20387 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____20396;
             FStar_Syntax_Syntax.vars = uu____20397;_},us)
          ->
          let uu____20403 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____20403 with
           | ((us',t),uu____20416) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____20422 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____20422)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____20438 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____20439 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____20449) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____20476 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____20476 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____20498  ->
                      match uu____20498 with
                      | (b,uu____20506) ->
                          let uu____20511 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____20511) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____20518 = universe_of_aux env res  in
                 level_of_type env res uu____20518  in
               let u_c =
                 let uu____20522 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____20522 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____20526 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____20526
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
            | FStar_Syntax_Syntax.Tm_bvar uu____20641 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____20658 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____20697 ->
                let uu____20698 = universe_of_aux env hd3  in
                (uu____20698, args1)
            | FStar_Syntax_Syntax.Tm_name uu____20713 ->
                let uu____20714 = universe_of_aux env hd3  in
                (uu____20714, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____20729 ->
                let uu____20742 = universe_of_aux env hd3  in
                (uu____20742, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____20757 ->
                let uu____20764 = universe_of_aux env hd3  in
                (uu____20764, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____20779 ->
                let uu____20806 = universe_of_aux env hd3  in
                (uu____20806, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____20821 ->
                let uu____20828 = universe_of_aux env hd3  in
                (uu____20828, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____20843 ->
                let uu____20844 = universe_of_aux env hd3  in
                (uu____20844, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____20859 ->
                let uu____20874 = universe_of_aux env hd3  in
                (uu____20874, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____20889 ->
                let uu____20896 = universe_of_aux env hd3  in
                (uu____20896, args1)
            | FStar_Syntax_Syntax.Tm_type uu____20911 ->
                let uu____20912 = universe_of_aux env hd3  in
                (uu____20912, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____20927,hd4::uu____20929) ->
                let uu____20994 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____20994 with
                 | (uu____21011,uu____21012,hd5) ->
                     let uu____21030 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____21030 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____21089 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env e
                   in
                let uu____21091 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____21091 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____21150 ->
                let uu____21151 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____21151 with
                 | (env1,uu____21175) ->
                     let env2 =
                       let uu___376_21181 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___376_21181.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___376_21181.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___376_21181.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___376_21181.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___376_21181.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___376_21181.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___376_21181.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___376_21181.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___376_21181.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___376_21181.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___376_21181.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___376_21181.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___376_21181.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___376_21181.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___376_21181.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___376_21181.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___376_21181.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___376_21181.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___376_21181.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___376_21181.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___376_21181.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___376_21181.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___376_21181.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___376_21181.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___376_21181.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___376_21181.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___376_21181.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___376_21181.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___376_21181.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___376_21181.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___376_21181.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___376_21181.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___376_21181.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___376_21181.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___376_21181.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___376_21181.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___376_21181.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___376_21181.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____21183 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____21183
                       then
                         let uu____21184 =
                           let uu____21185 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____21185  in
                         let uu____21186 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____21184 uu____21186
                       else ());
                      (let uu____21188 = tc_term env2 hd3  in
                       match uu____21188 with
                       | (uu____21211,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____21212;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____21214;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____21215;_},g)
                           ->
                           ((let uu____21229 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____21229
                               (fun a237  -> ()));
                            (t, args1)))))
             in
          let uu____21242 = type_of_head true hd1 args  in
          (match uu____21242 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____21288 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____21288 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____21342 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____21342)))
      | FStar_Syntax_Syntax.Tm_match (uu____21345,hd1::uu____21347) ->
          let uu____21412 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____21412 with
           | (uu____21415,uu____21416,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____21434,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____21481 = universe_of_aux env e  in
      level_of_type env e uu____21481
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____21506 = tc_binders env tps  in
      match uu____21506 with
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
      let uu____21560 =
        let uu____21561 = FStar_Syntax_Subst.compress t  in
        uu____21561.FStar_Syntax_Syntax.n  in
      match uu____21560 with
      | FStar_Syntax_Syntax.Tm_delayed uu____21566 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____21591 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____21596 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____21596
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____21598 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21598
            (fun uu____21612  ->
               match uu____21612 with
               | (t1,uu____21620) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____21622;
             FStar_Syntax_Syntax.vars = uu____21623;_},us)
          ->
          let uu____21629 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____21629
            (fun uu____21643  ->
               match uu____21643 with
               | (t1,uu____21651) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____21653 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____21653
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____21655 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____21655
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____21660;_})
          ->
          let mk_comp =
            let uu____21704 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____21704
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____21732 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____21732
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____21799 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____21799
                 (fun u  ->
                    let uu____21807 =
                      let uu____21810 =
                        let uu____21817 =
                          let uu____21818 =
                            let uu____21833 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____21833)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____21818  in
                        FStar_Syntax_Syntax.mk uu____21817  in
                      uu____21810 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____21807))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____21873 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____21873 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____21932 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____21932
                       (fun uc  ->
                          let uu____21940 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____21940)
                 | (x,imp)::bs3 ->
                     let uu____21966 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____21966
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____21975 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____21995) ->
          let uu____22000 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____22000
            (fun u_x  ->
               let uu____22008 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____22008)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____22054 =
              let uu____22055 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____22055.FStar_Syntax_Syntax.n  in
            match uu____22054 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____22137 = FStar_Util.first_N n_args bs  in
                    match uu____22137 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____22229 =
                          let uu____22234 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____22234  in
                        (match uu____22229 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____22294 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____22294 with
                       | (bs1,c1) ->
                           let uu____22315 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____22315
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____22393  ->
                     match uu____22393 with
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
                         let uu____22469 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____22469)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____22471) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____22477,uu____22478) ->
                aux t1
            | uu____22519 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22520,(FStar_Util.Inl t1,uu____22522),uu____22523) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____22570,(FStar_Util.Inr c,uu____22572),uu____22573) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____22638 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____22638
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____22646) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____22651 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____22674 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____22687 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____22698 = type_of_well_typed_term env t  in
      match uu____22698 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____22704;
            FStar_Syntax_Syntax.vars = uu____22705;_}
          -> FStar_Pervasives_Native.Some u
      | uu____22708 -> FStar_Pervasives_Native.None

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
            let uu___377_22733 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___377_22733.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___377_22733.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___377_22733.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___377_22733.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___377_22733.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___377_22733.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___377_22733.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___377_22733.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___377_22733.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___377_22733.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___377_22733.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___377_22733.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___377_22733.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___377_22733.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___377_22733.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___377_22733.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___377_22733.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___377_22733.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___377_22733.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___377_22733.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___377_22733.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___377_22733.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___377_22733.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___377_22733.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___377_22733.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___377_22733.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___377_22733.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___377_22733.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___377_22733.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___377_22733.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___377_22733.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___377_22733.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___377_22733.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___377_22733.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___377_22733.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___377_22733.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___377_22733.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___377_22733.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___377_22733.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___377_22733.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____22739 =
            if must_total
            then
              let uu____22740 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____22740 with | (uu____22747,uu____22748,g) -> g
            else
              (let uu____22751 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____22751 with | (uu____22758,uu____22759,g) -> g)
             in
          let uu____22761 =
            let uu____22762 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____22762  in
          if uu____22761
          then slow_check ()
          else
            (let uu____22764 = type_of_well_typed_term env2 t  in
             match uu____22764 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____22769 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____22769
                   then
                     let uu____22770 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____22771 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____22772 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____22773 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____22770 uu____22771 uu____22772 uu____22773
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____22777 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____22777
                    then
                      let uu____22778 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____22779 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____22780 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____22781 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____22778 (if b then "succeeded" else "failed")
                        uu____22779 uu____22780 uu____22781
                    else ());
                   if b
                   then FStar_TypeChecker_Env.trivial_guard
                   else slow_check ())))
  