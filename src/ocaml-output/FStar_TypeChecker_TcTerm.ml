open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___94_6 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___94_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___94_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___94_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___94_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___94_6.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___94_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___94_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___94_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___94_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___94_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___94_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___94_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___94_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___94_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___94_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___94_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___94_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___94_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___94_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___94_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___94_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___94_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___94_6.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___94_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___94_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___94_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___94_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___94_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___94_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___94_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___94_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___94_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice = (uu___94_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___94_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___94_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___94_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___94_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___94_6.FStar_TypeChecker_Env.dep_graph)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___95_12 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___95_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___95_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___95_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___95_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___95_12.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___95_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___95_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___95_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___95_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___95_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___95_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___95_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___95_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___95_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___95_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___95_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___95_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___95_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___95_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___95_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___95_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___95_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___95_12.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___95_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___95_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___95_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___95_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___95_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___95_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___95_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___95_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___95_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___95_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___95_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___95_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___95_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___95_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___95_12.FStar_TypeChecker_Env.dep_graph)
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
               let uu____59 =
                 let uu____68 = FStar_Syntax_Syntax.as_arg tl1  in [uu____68]
                  in
               uu____52 :: uu____59  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____51
              in
           uu____46 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___88_101  ->
    match uu___88_101 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____104 -> false
  
let steps :
  'Auu____111 . 'Auu____111 -> FStar_TypeChecker_Normalize.step Prims.list =
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
            | [] -> (t, FStar_TypeChecker_Rel.trivial_guard)
            | uu____194 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____206 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____206 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Rel.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____230 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____232 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____232
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____234 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____235 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____234 uu____235
                             in
                          let uu____236 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____236
                           in
                        let uu____241 =
                          let uu____254 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____255 =
                            let uu____256 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____256
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____254 env uu____255
                           in
                        match uu____241 with
                        | (s,uu____270,g0) ->
                            let uu____284 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____284 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____293 =
                                     FStar_TypeChecker_Rel.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____293
                                    in
                                 (s, g1)
                             | uu____294 -> fail1 ())))
             in
          aux false kt
  
let push_binding :
  'Auu____303 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____303) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____353 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____353
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
        (fun uu____373  ->
           let uu____374 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____374 t)
  
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
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____429 = FStar_Syntax_Syntax.mk_Total t  in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____429
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____432 =
            let uu____439 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____439 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                let uu____449 =
                  FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                    t'
                   in
                (match uu____449 with
                 | (e1,lc1) ->
                     let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                     let uu____463 =
                       FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                        in
                     (match uu____463 with
                      | (e2,g) ->
                          ((let uu____477 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____477
                            then
                              let uu____478 =
                                FStar_Syntax_Print.term_to_string t1  in
                              let uu____479 =
                                FStar_Syntax_Print.term_to_string t'  in
                              let uu____480 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              let uu____481 =
                                FStar_TypeChecker_Rel.guard_to_string env
                                  guard
                                 in
                              FStar_Util.print4
                                "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                uu____478 uu____479 uu____480 uu____481
                            else ());
                           (let msg =
                              let uu____489 =
                                FStar_TypeChecker_Rel.is_trivial_guard_formula
                                  g
                                 in
                              if uu____489
                              then FStar_Pervasives_Native.None
                              else
                                FStar_All.pipe_left
                                  (fun _0_16  ->
                                     FStar_Pervasives_Native.Some _0_16)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     t1 t')
                               in
                            let g1 = FStar_TypeChecker_Rel.conj_guard g guard
                               in
                            let uu____511 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e2 lc1 g1
                               in
                            match uu____511 with
                            | (lc2,g2) ->
                                let uu____524 = set_lcomp_result lc2 t'  in
                                ((memo_tk e2 t'), uu____524, g2)))))
             in
          match uu____432 with | (e1,lc1,g) -> (e1, lc1, g)
  
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
        let uu____561 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____561 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____571 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____571 with
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
        let uu____623 = ec  in
        match uu____623 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____646 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____646
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____648 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____648
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____650 =
              match copt with
              | FStar_Pervasives_Native.Some uu____663 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____666 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____668 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____668))
                     in
                  if uu____666
                  then
                    let uu____675 =
                      let uu____678 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____678  in
                    (uu____675, c)
                  else
                    (let uu____682 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____682
                     then
                       let uu____689 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____689)
                     else
                       (let uu____693 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____693
                        then
                          let uu____700 =
                            let uu____703 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____703  in
                          (uu____700, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____650 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____730 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____730
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____733 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Extreme
                           in
                        if uu____733
                        then
                          let uu____734 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____735 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____736 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e %s and c %s and expected_c %s\n"
                            uu____734 uu____735 uu____736
                        else ());
                       (let uu____738 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____738 with
                        | (e1,uu____752,g) ->
                            let g1 =
                              let uu____755 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____755
                                "could not prove post-condition" g
                               in
                            ((let uu____757 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____757
                              then
                                let uu____758 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____759 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect; guard is: %s\n"
                                  uu____758 uu____759
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
  'Auu____770 'Auu____771 .
    FStar_TypeChecker_Env.env ->
      ('Auu____770,'Auu____771,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____770,'Auu____771,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____793  ->
      match uu____793 with
      | (te,kt,f) ->
          let uu____803 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____803 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____811 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____816 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____811 uu____816)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____828 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____828 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____832 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____832
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____869 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____869 with
        | (head1,args) ->
            let uu____908 =
              let uu____923 =
                let uu____924 = FStar_Syntax_Util.un_uinst head1  in
                uu____924.FStar_Syntax_Syntax.n  in
              (uu____923, args)  in
            (match uu____908 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____940) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____965,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____966))::(hd1,FStar_Pervasives_Native.None
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
                fv,(uu____1039,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1040))::(pat,FStar_Pervasives_Native.None
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
             | uu____1122 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1151 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____1151)
            FStar_Pervasives_Native.tuple2 Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1187 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1194 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta] env pats
               in
            get_pat_vars uu____1187 uu____1194  in
          let uu____1195 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1222  ->
                    match uu____1222 with
                    | (b,uu____1228) ->
                        let uu____1229 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1229))
             in
          match uu____1195 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1235) ->
              let uu____1240 =
                let uu____1245 =
                  let uu____1246 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1246
                   in
                (FStar_Errors.Warning_PatternMissingBoundVar, uu____1245)  in
              FStar_Errors.log_issue rng uu____1240
  
let check_smt_pat :
  'Auu____1257 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,'Auu____1257) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____1298 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____1298
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____1299;
                  FStar_Syntax_Syntax.effect_name = uu____1300;
                  FStar_Syntax_Syntax.result_typ = uu____1301;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____1305)::[];
                  FStar_Syntax_Syntax.flags = uu____1306;_}
                -> check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs
            | uu____1351 -> failwith "Impossible"
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
              let uu___96_1411 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___96_1411.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___96_1411.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___96_1411.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___96_1411.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___96_1411.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___96_1411.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___96_1411.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___96_1411.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___96_1411.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___96_1411.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___96_1411.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___96_1411.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___96_1411.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___96_1411.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___96_1411.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___96_1411.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___96_1411.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___96_1411.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___96_1411.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___96_1411.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___96_1411.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___96_1411.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___96_1411.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___96_1411.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___96_1411.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___96_1411.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___96_1411.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___96_1411.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___96_1411.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___96_1411.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___96_1411.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___96_1411.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___96_1411.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___96_1411.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___96_1411.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___96_1411.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___96_1411.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___96_1411.FStar_TypeChecker_Env.dep_graph)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____1437 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____1437
               then
                 let uu____1438 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____1439 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____1438 uu____1439
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____1466  ->
                         match uu____1466 with
                         | (b,uu____1474) ->
                             let t =
                               let uu____1476 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____1476
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____1479 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____1480 -> []
                              | uu____1493 ->
                                  let uu____1494 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____1494])))
                  in
               let as_lex_list dec =
                 let uu____1507 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____1507 with
                 | (head1,uu____1525) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1549 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____1557 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___89_1566  ->
                         match uu___89_1566 with
                         | FStar_Syntax_Syntax.DECREASES uu____1567 -> true
                         | uu____1570 -> false))
                  in
               match uu____1557 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1576 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____1597 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1626 =
              match uu____1626 with
              | (l,t,u_names) ->
                  let uu____1650 =
                    let uu____1651 = FStar_Syntax_Subst.compress t  in
                    uu____1651.FStar_Syntax_Syntax.n  in
                  (match uu____1650 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1700  ->
                                 match uu____1700 with
                                 | (x,imp) ->
                                     let uu____1711 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1711
                                     then
                                       let uu____1716 =
                                         let uu____1717 =
                                           let uu____1720 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1720
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1717
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1716, imp)
                                     else (x, imp)))
                          in
                       let uu____1722 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1722 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1743 =
                                let uu____1748 =
                                  let uu____1749 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1756 =
                                    let uu____1765 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1765]  in
                                  uu____1749 :: uu____1756  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1748
                                 in
                              uu____1743 FStar_Pervasives_Native.None r  in
                            let uu____1792 = FStar_Util.prefix formals2  in
                            (match uu____1792 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___97_1839 = last1  in
                                   let uu____1840 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_1839.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_1839.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1840
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____1866 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1866
                                   then
                                     let uu____1867 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1868 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1869 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1867 uu____1868 uu____1869
                                   else ());
                                  (l, t', u_names))))
                   | uu____1873 ->
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
      tc_maybe_toplevel_term
        (let uu___98_2473 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___98_2473.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___98_2473.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___98_2473.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___98_2473.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___98_2473.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___98_2473.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___98_2473.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___98_2473.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___98_2473.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___98_2473.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___98_2473.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___98_2473.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___98_2473.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___98_2473.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___98_2473.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___98_2473.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___98_2473.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___98_2473.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___98_2473.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___98_2473.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___98_2473.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___98_2473.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___98_2473.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___98_2473.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___98_2473.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___98_2473.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___98_2473.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___98_2473.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___98_2473.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___98_2473.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___98_2473.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___98_2473.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___98_2473.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___98_2473.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___98_2473.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___98_2473.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___98_2473.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___98_2473.FStar_TypeChecker_Env.dep_graph)
         }) e

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
      (let uu____2485 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2485
       then
         let uu____2486 =
           let uu____2487 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2487  in
         let uu____2488 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____2486 uu____2488
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2497 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2528 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2535 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2550 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2551 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2552 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2553 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2554 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2571 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2584 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2591 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted
           (uu____2592,{
                         FStar_Syntax_Syntax.qkind =
                           FStar_Syntax_Syntax.Quote_static ;
                         FStar_Syntax_Syntax.antiquotes = aqs;_})
           when
           FStar_List.for_all
             (fun uu____2620  ->
                match uu____2620 with
                | (uu____2629,b,uu____2631) -> Prims.op_Negation b) aqs
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Rel.trivial_guard
       | FStar_Syntax_Syntax.Tm_quoted uu____2636 ->
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
           let uu____2650 =
             let uu____2657 =
               let uu____2662 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____2662  in
             value_check_expected_typ env1 top uu____2657
               FStar_TypeChecker_Rel.trivial_guard
              in
           (match uu____2650 with
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
             FStar_TypeChecker_Rel.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____2685 = tc_tot_or_gtot_term env1 e1  in
           (match uu____2685 with
            | (e2,c,g) ->
                let g1 =
                  let uu___99_2702 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___99_2702.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___99_2702.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___99_2702.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____2703 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____2703, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2722 = FStar_Syntax_Util.type_u ()  in
           (match uu____2722 with
            | (t,u) ->
                let uu____2735 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____2735 with
                 | (e2,c,g) ->
                     let uu____2751 =
                       let uu____2766 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2766 with
                       | (env2,uu____2788) -> tc_pats env2 pats  in
                     (match uu____2751 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___100_2822 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___100_2822.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___100_2822.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___100_2822.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____2823 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2826 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____2823, c, uu____2826))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2832 =
             let uu____2833 = FStar_Syntax_Subst.compress e1  in
             uu____2833.FStar_Syntax_Syntax.n  in
           (match uu____2832 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2842,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2844;
                               FStar_Syntax_Syntax.lbtyp = uu____2845;
                               FStar_Syntax_Syntax.lbeff = uu____2846;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____2848;
                               FStar_Syntax_Syntax.lbpos = uu____2849;_}::[]),e2)
                ->
                let uu____2877 =
                  let uu____2884 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____2884 e11  in
                (match uu____2877 with
                 | (e12,c1,g1) ->
                     let uu____2894 = tc_term env1 e2  in
                     (match uu____2894 with
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
                            let uu____2918 =
                              let uu____2925 =
                                let uu____2926 =
                                  let uu____2939 =
                                    let uu____2946 =
                                      let uu____2949 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____2949]  in
                                    (false, uu____2946)  in
                                  (uu____2939, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____2926  in
                              FStar_Syntax_Syntax.mk uu____2925  in
                            uu____2918 FStar_Pervasives_Native.None
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
                          let uu____2971 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____2971)))
            | uu____2972 ->
                let uu____2973 = tc_term env1 e1  in
                (match uu____2973 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2995) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____3007) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____3026 = tc_term env1 e1  in
           (match uu____3026 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____3050) ->
           let uu____3097 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____3097 with
            | (env0,uu____3111) ->
                let uu____3116 = tc_comp env0 expected_c  in
                (match uu____3116 with
                 | (expected_c1,uu____3130,g) ->
                     let uu____3132 =
                       let uu____3139 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____3139 e1  in
                     (match uu____3132 with
                      | (e2,c',g') ->
                          let uu____3149 =
                            let uu____3156 =
                              let uu____3161 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____3161)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____3156
                             in
                          (match uu____3149 with
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
                                 let uu____3215 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____3215
                                  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____3221 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____3221)
                                  in
                               let uu____3222 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____3222 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____3242) ->
           let uu____3289 = FStar_Syntax_Util.type_u ()  in
           (match uu____3289 with
            | (k,u) ->
                let uu____3302 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____3302 with
                 | (t1,uu____3316,f) ->
                     let uu____3318 =
                       let uu____3325 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____3325 e1  in
                     (match uu____3318 with
                      | (e2,c,g) ->
                          let uu____3335 =
                            let uu____3340 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____3345  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____3340 e2 c f
                             in
                          (match uu____3335 with
                           | (c1,f1) ->
                               let uu____3354 =
                                 let uu____3361 =
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
                                 comp_check_expected_typ env1 uu____3361 c1
                                  in
                               (match uu____3354 with
                                | (e3,c2,f2) ->
                                    let uu____3409 =
                                      let uu____3410 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3410
                                       in
                                    (e3, c2, uu____3409))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3411;
              FStar_Syntax_Syntax.vars = uu____3412;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3475 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3475 with
            | (unary_op,uu____3497) ->
                let head1 =
                  let uu____3521 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3521
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
              FStar_Syntax_Syntax.pos = uu____3559;
              FStar_Syntax_Syntax.vars = uu____3560;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3623 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3623 with
            | (unary_op,uu____3645) ->
                let head1 =
                  let uu____3669 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3669
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
                (FStar_Const.Const_reflect uu____3707);
              FStar_Syntax_Syntax.pos = uu____3708;
              FStar_Syntax_Syntax.vars = uu____3709;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3772 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3772 with
            | (unary_op,uu____3794) ->
                let head1 =
                  let uu____3818 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3818
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
              FStar_Syntax_Syntax.pos = uu____3856;
              FStar_Syntax_Syntax.vars = uu____3857;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3933 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3933 with
            | (unary_op,uu____3955) ->
                let head1 =
                  let uu____3979 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3979
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
              FStar_Syntax_Syntax.pos = uu____4023;
              FStar_Syntax_Syntax.vars = uu____4024;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____4054 =
             let uu____4061 =
               let uu____4062 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4062  in
             tc_term uu____4061 e1  in
           (match uu____4054 with
            | (e2,c,g) ->
                let uu____4086 = FStar_Syntax_Util.head_and_args top  in
                (match uu____4086 with
                 | (head1,uu____4108) ->
                     let uu____4129 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____4154 =
                       let uu____4155 =
                         let uu____4156 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____4156  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4155
                        in
                     (uu____4129, uu____4154, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4157;
              FStar_Syntax_Syntax.vars = uu____4158;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____4199 = FStar_Syntax_Util.head_and_args top  in
           (match uu____4199 with
            | (head1,uu____4221) ->
                let env' =
                  let uu____4243 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____4243  in
                let uu____4244 = tc_term env' r  in
                (match uu____4244 with
                 | (er,uu____4258,gr) ->
                     let uu____4260 = tc_term env1 t  in
                     (match uu____4260 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Rel.conj_guard gr gt1  in
                          let uu____4277 =
                            let uu____4278 =
                              let uu____4283 =
                                let uu____4284 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____4291 =
                                  let uu____4300 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____4300]  in
                                uu____4284 :: uu____4291  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____4283
                               in
                            uu____4278 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____4277, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____4327;
              FStar_Syntax_Syntax.vars = uu____4328;_},uu____4329)
           ->
           let uu____4350 =
             let uu____4355 =
               let uu____4356 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4356  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4355)  in
           FStar_Errors.raise_error uu____4350 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____4363;
              FStar_Syntax_Syntax.vars = uu____4364;_},uu____4365)
           ->
           let uu____4386 =
             let uu____4391 =
               let uu____4392 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____4392  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____4391)  in
           FStar_Errors.raise_error uu____4386 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____4399;
              FStar_Syntax_Syntax.vars = uu____4400;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____4433 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____4433 with
             | (env0,uu____4447) ->
                 let uu____4452 = tc_term env0 e1  in
                 (match uu____4452 with
                  | (e2,c,g) ->
                      let uu____4468 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____4468 with
                       | (reify_op,uu____4490) ->
                           let u_c =
                             let uu____4512 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____4512 with
                             | (uu____4519,c',uu____4521) ->
                                 let uu____4522 =
                                   let uu____4523 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____4523.FStar_Syntax_Syntax.n  in
                                 (match uu____4522 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____4527 ->
                                      let uu____4528 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____4528 with
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
                                                 let uu____4540 =
                                                   let uu____4541 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____4542 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____4543 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____4541 uu____4542
                                                     uu____4543
                                                    in
                                                 failwith uu____4540);
                                            u)))
                              in
                           let repr =
                             let uu____4545 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____4545
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
                             let uu____4574 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____4574
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____4575 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____4575 with
                            | (e4,c2,g') ->
                                let uu____4591 =
                                  FStar_TypeChecker_Rel.conj_guard g g'  in
                                (e4, c2, uu____4591))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____4593;
              FStar_Syntax_Syntax.vars = uu____4594;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____4638 =
               let uu____4639 =
                 let uu____4644 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____4644)  in
               FStar_Errors.raise_error uu____4639 e1.FStar_Syntax_Syntax.pos
                in
             let uu____4651 = FStar_Syntax_Util.head_and_args top  in
             match uu____4651 with
             | (reflect_op,uu____4673) ->
                 let uu____4694 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____4694 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____4727 =
                        let uu____4728 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____4728  in
                      if uu____4727
                      then no_reflect ()
                      else
                        (let uu____4738 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____4738 with
                         | (env_no_ex,topt) ->
                             let uu____4757 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____4777 =
                                   let uu____4784 =
                                     let uu____4785 =
                                       let uu____4800 =
                                         let uu____4809 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____4816 =
                                           let uu____4825 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____4825]  in
                                         uu____4809 :: uu____4816  in
                                       (repr, uu____4800)  in
                                     FStar_Syntax_Syntax.Tm_app uu____4785
                                      in
                                   FStar_Syntax_Syntax.mk uu____4784  in
                                 uu____4777 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____4863 =
                                 let uu____4870 =
                                   let uu____4871 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____4871
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____4870 t  in
                               match uu____4863 with
                               | (t1,uu____4897,g) ->
                                   let uu____4899 =
                                     let uu____4900 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____4900.FStar_Syntax_Syntax.n  in
                                   (match uu____4899 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4913,(res,uu____4915)::
                                         (wp,uu____4917)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4958 -> failwith "Impossible")
                                in
                             (match uu____4757 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4983 =
                                    let uu____4990 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____4990 with
                                    | (e2,c,g) ->
                                        ((let uu____5007 =
                                            let uu____5008 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____5008
                                             in
                                          if uu____5007
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____5022 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____5022 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____5032 =
                                                  let uu____5041 =
                                                    let uu____5048 =
                                                      let uu____5049 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____5050 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____5049 uu____5050
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____5048,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____5041]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____5032);
                                               (let uu____5063 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____5063)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____5067 =
                                                let uu____5068 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____5068
                                                 in
                                              (e2, uu____5067)))
                                     in
                                  (match uu____4983 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____5084 =
                                           let uu____5085 =
                                             let uu____5086 =
                                               let uu____5087 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____5087]  in
                                             let uu____5088 =
                                               let uu____5097 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____5097]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____5086;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____5088;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____5085
                                            in
                                         FStar_All.pipe_right uu____5084
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____5143 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____5143 with
                                        | (e4,c1,g') ->
                                            let uu____5159 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____5159))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args head1.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____5206 =
               let uu____5207 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____5207 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____5206 instantiate_both  in
           ((let uu____5223 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____5223
             then
               let uu____5224 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____5225 = FStar_Syntax_Print.term_to_string top  in
               let uu____5226 =
                 let uu____5227 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____5227
                   (fun uu___90_5233  ->
                      match uu___90_5233 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____5224
                 uu____5225 uu____5226
             else ());
            (let uu____5238 = tc_term (no_inst env2) head1  in
             match uu____5238 with
             | (head2,chead,g_head) ->
                 let uu____5254 =
                   let uu____5261 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____5263 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____5263))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____5261
                   then
                     let uu____5270 =
                       let uu____5277 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____5277
                        in
                     match uu____5270 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____5290 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____5290)
                    in
                 (match uu____5254 with
                  | (e1,c,g) ->
                      ((let uu____5303 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____5303
                        then
                          let uu____5304 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____5304
                        else ());
                       (let uu____5306 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____5306 with
                        | (e2,c1,g') ->
                            let gres = FStar_TypeChecker_Rel.conj_guard g g'
                               in
                            ((let uu____5324 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____5324
                              then
                                let uu____5325 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____5326 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____5325 uu____5326
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____5366 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5366 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____5386 = tc_term env12 e1  in
                (match uu____5386 with
                 | (e11,c1,g1) ->
                     let uu____5402 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____5416 = FStar_Syntax_Util.type_u ()  in
                           (match uu____5416 with
                            | (k,uu____5428) ->
                                let uu____5429 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____5429 with
                                 | (res_t,uu____5449,g) ->
                                     let uu____5463 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____5464 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g
                                        in
                                     (uu____5463, res_t, uu____5464)))
                        in
                     (match uu____5402 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____5475 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____5475
                            then
                              let uu____5476 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____5476
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
                            let uu____5597 =
                              let uu____5602 =
                                FStar_List.fold_right
                                  (fun uu____5681  ->
                                     fun uu____5682  ->
                                       match (uu____5681, uu____5682) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5916 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5916)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____5602 with
                              | (cases,g) ->
                                  let uu____6014 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____6014, g)
                               in
                            match uu____5597 with
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
                                           (fun uu____6154  ->
                                              match uu____6154 with
                                              | ((pat,wopt,br),uu____6198,eff_label,uu____6200,uu____6201,uu____6202)
                                                  ->
                                                  let uu____6237 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____6237)))
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
                                  let uu____6304 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____6304
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____6309 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____6309  in
                                     let lb =
                                       let uu____6313 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____6313 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____6319 =
                                         let uu____6326 =
                                           let uu____6327 =
                                             let uu____6340 =
                                               let uu____6343 =
                                                 let uu____6344 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____6344]  in
                                               FStar_Syntax_Subst.close
                                                 uu____6343 e_match
                                                in
                                             ((false, [lb]), uu____6340)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____6327
                                            in
                                         FStar_Syntax_Syntax.mk uu____6326
                                          in
                                       uu____6319
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____6371 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____6371
                                  then
                                    let uu____6372 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6373 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____6372 uu____6373
                                  else ());
                                 (let uu____6375 =
                                    FStar_TypeChecker_Rel.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____6375))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____6376;
                FStar_Syntax_Syntax.lbunivs = uu____6377;
                FStar_Syntax_Syntax.lbtyp = uu____6378;
                FStar_Syntax_Syntax.lbeff = uu____6379;
                FStar_Syntax_Syntax.lbdef = uu____6380;
                FStar_Syntax_Syntax.lbattrs = uu____6381;
                FStar_Syntax_Syntax.lbpos = uu____6382;_}::[]),uu____6383)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____6406),uu____6407) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____6422;
                FStar_Syntax_Syntax.lbunivs = uu____6423;
                FStar_Syntax_Syntax.lbtyp = uu____6424;
                FStar_Syntax_Syntax.lbeff = uu____6425;
                FStar_Syntax_Syntax.lbdef = uu____6426;
                FStar_Syntax_Syntax.lbattrs = uu____6427;
                FStar_Syntax_Syntax.lbpos = uu____6428;_}::uu____6429),uu____6430)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____6455),uu____6456) ->
           check_inner_let_rec env1 top)

and (tc_synth :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        let uu____6482 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____6522))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____6555 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____6482 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6587 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____6587 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6591 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6591)
               in
            let uu____6592 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____6592 with
             | (env',uu____6606) ->
                 let uu____6611 = tc_term env' typ  in
                 (match uu____6611 with
                  | (typ1,uu____6625,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6628 = tc_tactic env' tau  in
                        match uu____6628 with
                        | (tau1,uu____6642,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6650 =
                                    let uu____6655 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid
                                       in
                                    let uu____6656 =
                                      let uu____6657 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit
                                         in
                                      [uu____6657]  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6655
                                      uu____6656
                                     in
                                  uu____6650 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth_hook
                                       env' typ1
                                       (let uu___101_6681 = tau1  in
                                        {
                                          FStar_Syntax_Syntax.n =
                                            (uu___101_6681.FStar_Syntax_Syntax.n);
                                          FStar_Syntax_Syntax.pos = rng;
                                          FStar_Syntax_Syntax.vars =
                                            (uu___101_6681.FStar_Syntax_Syntax.vars)
                                        })
                                      in
                                   (let uu____6683 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac")
                                       in
                                    if uu____6683
                                    then
                                      let uu____6684 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print1 "Got %s\n" uu____6684
                                    else ());
                                   t)
                                 in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6687 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____6687)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___102_6691 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___102_6691.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___102_6691.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___102_6691.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___102_6691.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___102_6691.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___102_6691.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___102_6691.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___102_6691.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___102_6691.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___102_6691.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___102_6691.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___102_6691.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___102_6691.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___102_6691.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___102_6691.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___102_6691.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___102_6691.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___102_6691.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___102_6691.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___102_6691.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___102_6691.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___102_6691.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___102_6691.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___102_6691.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___102_6691.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___102_6691.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___102_6691.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___102_6691.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___102_6691.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___102_6691.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___102_6691.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___102_6691.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___102_6691.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___102_6691.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___102_6691.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___102_6691.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___102_6691.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___102_6691.FStar_TypeChecker_Env.dep_graph)
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
        let uu___103_6695 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___103_6695.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___103_6695.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___103_6695.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___103_6695.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___103_6695.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___103_6695.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___103_6695.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___103_6695.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___103_6695.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___103_6695.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___103_6695.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___103_6695.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___103_6695.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___103_6695.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___103_6695.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___103_6695.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___103_6695.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___103_6695.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___103_6695.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___103_6695.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___103_6695.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___103_6695.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___103_6695.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___103_6695.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___103_6695.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___103_6695.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___103_6695.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___103_6695.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___103_6695.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___103_6695.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___103_6695.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___103_6695.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___103_6695.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___103_6695.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___103_6695.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___103_6695.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___103_6695.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___103_6695.FStar_TypeChecker_Env.dep_graph)
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
          let uu____6711 = tc_tactic env tactic  in
          (match uu____6711 with
           | (tactic1,uu____6721,uu____6722) ->
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
        let uu____6771 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____6771 with
        | (e2,t,implicits) ->
            let tc =
              let uu____6792 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6792
              then FStar_Util.Inl t
              else
                (let uu____6798 =
                   let uu____6799 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6799
                    in
                 FStar_Util.Inr uu____6798)
               in
            let is_data_ctor uu___91_6807 =
              match uu___91_6807 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6810) -> true
              | uu____6817 -> false  in
            let uu____6820 =
              (is_data_ctor dc) &&
                (let uu____6822 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6822)
               in
            if uu____6820
            then
              let uu____6829 =
                let uu____6834 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6834)  in
              let uu____6835 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6829 uu____6835
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6852 =
            let uu____6853 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6853
             in
          failwith uu____6852
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____6882 =
            let uu____6887 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____6887  in
          value_check_expected_typ env1 e uu____6882
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6889 =
            let uu____6902 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6902 with
            | FStar_Pervasives_Native.None  ->
                let uu____6917 = FStar_Syntax_Util.type_u ()  in
                (match uu____6917 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6889 with
           | (t,uu____6954,g0) ->
               let uu____6968 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6968 with
                | (e1,uu____6988,g1) ->
                    let uu____7002 =
                      let uu____7003 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____7003
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____7004 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____7002, uu____7004)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____7006 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____7015 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____7015)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____7006 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___104_7028 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___104_7028.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___104_7028.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____7031 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____7031 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____7052 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____7052
                       then FStar_Util.Inl t1
                       else
                         (let uu____7058 =
                            let uu____7059 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____7059
                             in
                          FStar_Util.Inr uu____7058)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7061;
             FStar_Syntax_Syntax.vars = uu____7062;_},uu____7063)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____7068 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____7068
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____7076 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____7076
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7084;
             FStar_Syntax_Syntax.vars = uu____7085;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____7094 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7094 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____7117 =
                     let uu____7122 =
                       let uu____7123 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____7124 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____7125 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____7123 uu____7124 uu____7125
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____7122)
                      in
                   let uu____7126 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____7117 uu____7126)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____7142 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____7146 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____7146 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7148 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7148 with
           | ((us,t),range) ->
               ((let uu____7171 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____7171
                 then
                   let uu____7172 =
                     let uu____7173 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____7173  in
                   let uu____7174 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____7175 = FStar_Range.string_of_range range  in
                   let uu____7176 = FStar_Range.string_of_use_range range  in
                   let uu____7177 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____7172 uu____7174 uu____7175 uu____7176 uu____7177
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____7182 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____7182 us  in
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
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7206 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7206 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____7220 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____7220 with
                | (env2,uu____7234) ->
                    let uu____7239 = tc_binders env2 bs1  in
                    (match uu____7239 with
                     | (bs2,env3,g,us) ->
                         let uu____7258 = tc_comp env3 c1  in
                         (match uu____7258 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___105_7277 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___105_7277.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___105_7277.FStar_Syntax_Syntax.vars)
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
                                  let uu____7286 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____7286
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
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____7302 =
            let uu____7307 =
              let uu____7308 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____7308]  in
            FStar_Syntax_Subst.open_term uu____7307 phi  in
          (match uu____7302 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____7330 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____7330 with
                | (env2,uu____7344) ->
                    let uu____7349 =
                      let uu____7362 = FStar_List.hd x1  in
                      tc_binder env2 uu____7362  in
                    (match uu____7349 with
                     | (x2,env3,f1,u) ->
                         ((let uu____7390 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____7390
                           then
                             let uu____7391 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____7392 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7393 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____7391 uu____7392 uu____7393
                           else ());
                          (let uu____7395 = FStar_Syntax_Util.type_u ()  in
                           match uu____7395 with
                           | (t_phi,uu____7407) ->
                               let uu____7408 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____7408 with
                                | (phi2,uu____7422,f2) ->
                                    let e1 =
                                      let uu___106_7427 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___106_7427.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___106_7427.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____7434 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____7434
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____7454) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____7477 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____7477
            then
              let uu____7478 =
                FStar_Syntax_Print.term_to_string
                  (let uu___107_7481 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___107_7481.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___107_7481.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____7478
            else ());
           (let uu____7493 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____7493 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____7506 ->
          let uu____7507 =
            let uu____7508 = FStar_Syntax_Print.term_to_string top  in
            let uu____7509 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7508
              uu____7509
             in
          failwith uu____7507

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7519 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7520,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7531,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7547 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7552 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7553 ->
            let uu____7554 =
              let uu____7559 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____7559 FStar_Util.must  in
            FStar_All.pipe_right uu____7554 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7584 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7585 =
              let uu____7590 =
                let uu____7591 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7591
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7590)  in
            FStar_Errors.raise_error uu____7585 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7592 =
              let uu____7597 =
                let uu____7598 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7598
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7597)  in
            FStar_Errors.raise_error uu____7592 r
        | FStar_Const.Const_reify  ->
            let uu____7599 =
              let uu____7604 =
                let uu____7605 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7605
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7604)  in
            FStar_Errors.raise_error uu____7599 r
        | FStar_Const.Const_reflect uu____7606 ->
            let uu____7607 =
              let uu____7612 =
                let uu____7613 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7613
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7612)  in
            FStar_Errors.raise_error uu____7607 r
        | uu____7614 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____7631) ->
          let uu____7640 = FStar_Syntax_Util.type_u ()  in
          (match uu____7640 with
           | (k,u) ->
               let uu____7653 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7653 with
                | (t1,uu____7667,g) ->
                    let uu____7669 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7669, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7671) ->
          let uu____7680 = FStar_Syntax_Util.type_u ()  in
          (match uu____7680 with
           | (k,u) ->
               let uu____7693 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7693 with
                | (t1,uu____7707,g) ->
                    let uu____7709 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7709, u, g)))
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
            let uu____7719 =
              let uu____7724 =
                let uu____7725 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7725 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7724  in
            uu____7719 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7740 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7740 with
           | (tc1,uu____7754,f) ->
               let uu____7756 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7756 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7800 =
                        let uu____7801 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7801.FStar_Syntax_Syntax.n  in
                      match uu____7800 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7804,us) -> us
                      | uu____7810 -> []  in
                    let uu____7811 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7811 with
                     | (uu____7832,args1) ->
                         let uu____7854 =
                           let uu____7873 = FStar_List.hd args1  in
                           let uu____7886 = FStar_List.tl args1  in
                           (uu____7873, uu____7886)  in
                         (match uu____7854 with
                          | (res,args2) ->
                              let uu____7951 =
                                let uu____7960 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___92_7988  ->
                                          match uu___92_7988 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7996 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7996 with
                                               | (env1,uu____8008) ->
                                                   let uu____8013 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____8013 with
                                                    | (e1,uu____8025,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7960
                                  FStar_List.unzip
                                 in
                              (match uu____7951 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___108_8064 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___108_8064.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___108_8064.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____8068 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____8068 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____8072 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____8072))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____8082 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____8083 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____8093 = aux u3  in FStar_Syntax_Syntax.U_succ uu____8093
        | FStar_Syntax_Syntax.U_max us ->
            let uu____8097 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____8097
        | FStar_Syntax_Syntax.U_name x ->
            let uu____8101 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____8101
            then u2
            else
              (let uu____8103 =
                 let uu____8104 =
                   let uu____8105 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____8105 " not found"  in
                 Prims.strcat "Universe variable " uu____8104  in
               failwith uu____8103)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____8107 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____8107 FStar_Pervasives_Native.snd
         | uu____8116 -> aux u)

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
            let uu____8145 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____8145 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____8263 bs2 bs_expected1 =
              match uu____8263 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____8495)) ->
                             let uu____8500 =
                               let uu____8505 =
                                 let uu____8506 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8506
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8505)
                                in
                             let uu____8507 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8500 uu____8507
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____8508),FStar_Pervasives_Native.None ) ->
                             let uu____8513 =
                               let uu____8518 =
                                 let uu____8519 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8519
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8518)
                                in
                             let uu____8520 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8513 uu____8520
                         | uu____8521 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____8531 =
                           let uu____8538 =
                             let uu____8539 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____8539.FStar_Syntax_Syntax.n  in
                           match uu____8538 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____8550 ->
                               ((let uu____8552 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____8552
                                 then
                                   let uu____8553 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____8553
                                 else ());
                                (let uu____8555 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____8555 with
                                 | (t,uu____8569,g1) ->
                                     let g2 =
                                       let uu____8572 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____8572
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____8574 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____8574 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____8577 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____8582 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____8577 uu____8582
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____8584 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____8584
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____8586 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____8586
                                        in
                                     (t, g3)))
                            in
                         match uu____8531 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___109_8632 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___109_8632.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___109_8632.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____8645 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____8645
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
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected
             in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____8897 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8906 = tc_binders env1 bs  in
                  match uu____8906 with
                  | (bs1,envbody,g,uu____8936) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8986 =
                    let uu____8987 = FStar_Syntax_Subst.compress t2  in
                    uu____8987.FStar_Syntax_Syntax.n  in
                  match uu____8986 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____9018 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____9040 -> failwith "Impossible");
                       (let uu____9049 = tc_binders env1 bs  in
                        match uu____9049 with
                        | (bs1,envbody,g,uu____9089) ->
                            let uu____9090 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____9090 with
                             | (envbody1,uu____9126) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____9145;
                         FStar_Syntax_Syntax.pos = uu____9146;
                         FStar_Syntax_Syntax.vars = uu____9147;_},uu____9148)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____9190 -> failwith "Impossible");
                       (let uu____9199 = tc_binders env1 bs  in
                        match uu____9199 with
                        | (bs1,envbody,g,uu____9239) ->
                            let uu____9240 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____9240 with
                             | (envbody1,uu____9276) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____9296) ->
                      let uu____9301 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____9301 with
                       | (uu____9358,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____9425 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____9425 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____9562 c_expected2 body3
                               =
                               match uu____9562 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____9666 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____9666, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____9681 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____9681
                                           in
                                        let uu____9682 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____9682, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____9697 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____9697
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
                                               let uu____9753 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____9753 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____9778 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____9778 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9830 =
                                                           let uu____9855 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9855,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____9830
                                                           c_expected4 body3))
                                           | uu____9874 ->
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
                             let uu____9898 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____9898 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___110_9959 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___110_9959.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___110_9959.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___110_9959.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___110_9959.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___110_9959.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___110_9959.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___110_9959.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___110_9959.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___110_9959.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___110_9959.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___110_9959.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___110_9959.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___110_9959.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___110_9959.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___110_9959.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___110_9959.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___110_9959.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___110_9959.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___110_9959.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___110_9959.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___110_9959.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___110_9959.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___110_9959.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___110_9959.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___110_9959.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___110_9959.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___110_9959.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___110_9959.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___110_9959.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___110_9959.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___110_9959.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___110_9959.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___110_9959.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___110_9959.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___110_9959.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___110_9959.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___110_9959.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___110_9959.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____10017  ->
                                     fun uu____10018  ->
                                       match (uu____10017, uu____10018) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____10100 =
                                             let uu____10107 =
                                               let uu____10108 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10108
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____10107 t3  in
                                           (match uu____10100 with
                                            | (t4,uu____10130,uu____10131) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____10143 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___111_10146
                                                             = x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___111_10146.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___111_10146.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____10143 ::
                                                        letrec_binders
                                                  | uu____10147 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____10156 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____10156 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____10224 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____10224 with
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
                  | uu____10280 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____10309 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____10309
                      else
                        (let uu____10311 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____10311 with
                         | (uu____10358,bs1,uu____10360,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____10388 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____10388 with
          | (env1,topt) ->
              ((let uu____10408 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____10408
                then
                  let uu____10409 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____10409
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____10413 = expected_function_typ1 env1 topt body  in
                match uu____10413 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____10453 =
                      let should_check_expected_effect =
                        let uu____10465 =
                          let uu____10472 =
                            let uu____10473 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____10473.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____10472)  in
                        match uu____10465 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____10478,(FStar_Util.Inr
                                         expected_c,uu____10480),uu____10481))
                            -> false
                        | uu____10530 -> true  in
                      let uu____10537 =
                        tc_term
                          (let uu___112_10546 = envbody  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___112_10546.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___112_10546.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___112_10546.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___112_10546.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___112_10546.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___112_10546.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___112_10546.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___112_10546.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___112_10546.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___112_10546.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___112_10546.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___112_10546.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___112_10546.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___112_10546.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___112_10546.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___112_10546.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___112_10546.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___112_10546.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___112_10546.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___112_10546.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___112_10546.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___112_10546.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___112_10546.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___112_10546.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___112_10546.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___112_10546.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___112_10546.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___112_10546.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___112_10546.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___112_10546.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___112_10546.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___112_10546.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___112_10546.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___112_10546.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___112_10546.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___112_10546.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___112_10546.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____10537 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____10571 =
                              let uu____10578 =
                                let uu____10583 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody  in
                                (body2, uu____10583)  in
                              check_expected_effect
                                (let uu___113_10586 = envbody  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___113_10586.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___113_10586.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___113_10586.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___113_10586.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___113_10586.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___113_10586.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___113_10586.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___113_10586.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___113_10586.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___113_10586.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___113_10586.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___113_10586.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___113_10586.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___113_10586.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___113_10586.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___113_10586.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___113_10586.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___113_10586.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___113_10586.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___113_10586.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___113_10586.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___113_10586.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___113_10586.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___113_10586.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___113_10586.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___113_10586.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___113_10586.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___113_10586.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___113_10586.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___113_10586.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___113_10586.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___113_10586.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___113_10586.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___113_10586.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___113_10586.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___113_10586.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___113_10586.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___113_10586.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____10578
                               in
                            (match uu____10571 with
                             | (body3,cbody1,guard) ->
                                 let uu____10600 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____10600))
                          else
                            (let uu____10606 =
                               FStar_Syntax_Syntax.lcomp_comp cbody  in
                             (body2, uu____10606, guard_body1))
                       in
                    (match uu____10453 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____10631 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____10633 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____10633)
                              in
                           if uu____10631
                           then
                             let uu____10634 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____10634
                           else
                             (let guard1 =
                                let uu____10637 =
                                  FStar_TypeChecker_Rel.conj_guard g guard
                                   in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____10637
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
                         let uu____10649 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____10670 ->
                                    (e, t1, guard2)
                                | uu____10683 ->
                                    let uu____10684 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____10684 with
                                     | (e1,guard') ->
                                         let uu____10697 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard2 guard'
                                            in
                                         (e1, t1, uu____10697)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard2)
                            in
                         (match uu____10649 with
                          | (e1,tfun,guard3) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun  in
                              let uu____10708 =
                                let uu____10713 =
                                  FStar_Syntax_Util.lcomp_of_comp c  in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____10713 guard3
                                 in
                              (match uu____10708 with
                               | (c1,g1) -> (e1, c1, g1))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
              (let uu____10757 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____10757
               then
                 let uu____10758 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____10759 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____10758
                   uu____10759
               else ());
              (let monadic_application uu____10832 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____10832 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____10895 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____10895 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___114_10909 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___114_10909.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___114_10909.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___114_10909.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____10910 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____10924 =
                                    FStar_TypeChecker_Rel.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Rel.conj_guard g0)
                                    uu____10924
                                   in
                                (cres1, g)
                            | uu____10925 ->
                                let g =
                                  let uu____10933 =
                                    let uu____10934 =
                                      FStar_TypeChecker_Rel.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____10934
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g0
                                    uu____10933
                                   in
                                let uu____10935 =
                                  let uu____10936 =
                                    let uu____10937 =
                                      let uu____10938 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____10938
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____10937
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____10936
                                   in
                                (uu____10935, g)
                             in
                          (match uu____10910 with
                           | (cres2,guard1) ->
                               ((let uu____10950 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____10950
                                 then
                                   let uu____10951 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____10951
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____10967  ->
                                             match uu____10967 with
                                             | (uu____10976,uu____10977,lc)
                                                 ->
                                                 (let uu____10985 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____10985)
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
                                   let uu____10995 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____10995
                                   then
                                     ((let uu____10997 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____10997
                                       then
                                         let uu____10998 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____10998
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____11002 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____11002
                                       then
                                         let uu____11003 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____11003
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____11029  ->
                                          match uu____11029 with
                                          | ((e,q),x,c) ->
                                              ((let uu____11063 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____11063
                                                then
                                                  let uu____11064 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____11066 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  FStar_Util.print2
                                                    "(b) Monadic app: Binding argument %s : %s\n"
                                                    uu____11064 uu____11066
                                                else ());
                                               (let uu____11068 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____11068
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
                                   (let uu____11076 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____11076
                                    then
                                      let uu____11077 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s "
                                        uu____11077
                                    else ());
                                   (let uu____11079 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____11079
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
                                   let uu____11087 =
                                     let uu____11088 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____11088.FStar_Syntax_Syntax.n  in
                                   match uu____11087 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____11092 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____11113  ->
                                              match uu____11113 with
                                              | (arg,uu____11127,uu____11128)
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
                                     (let uu____11138 =
                                        let map_fun uu____11196 =
                                          match uu____11196 with
                                          | ((e,q),uu____11229,c) ->
                                              let uu____11239 =
                                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                  c
                                                 in
                                              if uu____11239
                                              then
                                                (FStar_Pervasives_Native.None,
                                                  (e, q))
                                              else
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
                                                 let uu____11283 =
                                                   let uu____11288 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       x
                                                      in
                                                   (uu____11288, q)  in
                                                 ((FStar_Pervasives_Native.Some
                                                     (x,
                                                       (c.FStar_Syntax_Syntax.eff_name),
                                                       (c.FStar_Syntax_Syntax.res_typ),
                                                       e1)), uu____11283))
                                           in
                                        let uu____11311 =
                                          let uu____11338 =
                                            let uu____11363 =
                                              let uu____11374 =
                                                let uu____11383 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____11383,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____11374 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____11363
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____11338
                                           in
                                        match uu____11311 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____11560 =
                                              let uu____11561 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____11561
                                               in
                                            let uu____11570 =
                                              let uu____11571 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____11571  in
                                            (lifted_args, uu____11560,
                                              uu____11570)
                                         in
                                      match uu____11138 with
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
                                            uu___93_11670 =
                                            match uu___93_11670 with
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
                                                  let uu____11731 =
                                                    let uu____11738 =
                                                      let uu____11739 =
                                                        let uu____11752 =
                                                          let uu____11755 =
                                                            let uu____11756 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____11756]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____11755 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____11752)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____11739
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____11738
                                                     in
                                                  uu____11731
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
                                 let uu____11802 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____11802 with
                                 | (comp3,g) ->
                                     ((let uu____11819 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____11819
                                       then
                                         let uu____11820 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____11821 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____11820 uu____11821
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____11897 bs args1 =
                 match uu____11897 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____12030))::rest,
                         (uu____12032,FStar_Pervasives_Native.None )::uu____12033)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____12093 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____12093 with
                           | (t1,g_ex) ->
                               let uu____12106 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____12106 with
                                | (varg,uu____12126,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____12152 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____12152)  in
                                    let uu____12155 =
                                      let uu____12188 =
                                        let uu____12199 =
                                          let uu____12208 =
                                            let uu____12209 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____12209
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____12208)
                                           in
                                        uu____12199 :: outargs  in
                                      let uu____12220 =
                                        let uu____12221 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_ex g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          implicits uu____12221
                                         in
                                      (subst2, uu____12188, (arg ::
                                        arg_rets), uu____12220, fvs)
                                       in
                                    tc_args head_info uu____12155 rest args1))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____12323),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____12324)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____12337 ->
                                let uu____12346 =
                                  let uu____12351 =
                                    let uu____12352 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____12353 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____12354 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____12355 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____12352 uu____12353 uu____12354
                                      uu____12355
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____12351)
                                   in
                                FStar_Errors.raise_error uu____12346
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___115_12358 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___115_12358.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___115_12358.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____12360 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____12360
                             then
                               let uu____12361 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____12362 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____12363 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12364 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____12365 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____12361 uu____12362 uu____12363
                                 uu____12364 uu____12365
                             else ());
                            (let uu____12367 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____12367 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___116_12382 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___116_12382.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___116_12382.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___116_12382.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___116_12382.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___116_12382.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___116_12382.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___116_12382.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___116_12382.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___116_12382.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___116_12382.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___116_12382.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___116_12382.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___116_12382.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___116_12382.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___116_12382.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___116_12382.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___116_12382.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___116_12382.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___116_12382.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___116_12382.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___116_12382.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___116_12382.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___116_12382.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___116_12382.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___116_12382.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___116_12382.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___116_12382.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___116_12382.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___116_12382.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___116_12382.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___116_12382.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___116_12382.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___116_12382.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___116_12382.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___116_12382.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___116_12382.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___116_12382.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___116_12382.FStar_TypeChecker_Env.dep_graph)
                                   }  in
                                 ((let uu____12384 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____12384
                                   then
                                     let uu____12385 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____12386 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____12387 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____12385 uu____12386 uu____12387
                                   else ());
                                  (let uu____12389 = tc_term env2 e  in
                                   match uu____12389 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____12406 =
                                           FStar_TypeChecker_Rel.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Rel.conj_guard
                                              g_ex) uu____12406
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____12423 =
                                           let uu____12426 =
                                             let uu____12433 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____12433
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____12426
                                            in
                                         (uu____12423, aq)  in
                                       let uu____12438 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____12438
                                       then
                                         let subst2 =
                                           let uu____12446 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____12446 e1
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
                      | (uu____12532,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____12568) ->
                          let uu____12619 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____12619 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____12669 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____12669
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____12696 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____12696 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____12718 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____12718)
                                             in
                                          ((let uu____12720 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____12720
                                            then
                                              FStar_Errors.log_issue
                                                tres1.FStar_Syntax_Syntax.pos
                                                (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                  "Potentially redundant explicit currying of a function type")
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____12758 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____12766 =
                                         let uu____12767 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____12767.FStar_Syntax_Syntax.n
                                          in
                                       match uu____12766 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____12770;
                                              FStar_Syntax_Syntax.index =
                                                uu____12771;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____12773)
                                           -> norm_tres tres4
                                       | uu____12780 -> tres3  in
                                     let uu____12781 = norm_tres tres1  in
                                     aux true solve ghead2 uu____12781
                                 | uu____12782 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____12784 ->
                                     let uu____12785 =
                                       let uu____12790 =
                                         let uu____12791 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____12792 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____12799 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____12791 uu____12792
                                           uu____12799
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____12790)
                                        in
                                     let uu____12800 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____12785
                                       uu____12800
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____12828 =
                   let uu____12829 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____12829.FStar_Syntax_Syntax.n  in
                 match uu____12828 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____12838 ->
                     let uu____12853 =
                       FStar_List.fold_right
                         (fun uu____12882  ->
                            fun uu____12883  ->
                              match uu____12883 with
                              | (bs,guard1) ->
                                  let uu____12908 =
                                    let uu____12921 =
                                      let uu____12922 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____12922
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____12921
                                     in
                                  (match uu____12908 with
                                   | (t,uu____12938,g) ->
                                       let uu____12952 =
                                         let uu____12955 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____12955 :: bs  in
                                       let uu____12956 =
                                         FStar_TypeChecker_Rel.conj_guard g
                                           guard1
                                          in
                                       (uu____12952, uu____12956))) args
                         ([], guard)
                        in
                     (match uu____12853 with
                      | (bs,guard1) ->
                          let uu____12973 =
                            let uu____12980 =
                              let uu____12993 =
                                let uu____12994 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____12994
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____12993
                               in
                            match uu____12980 with
                            | (t,uu____13010,g) ->
                                let uu____13024 = FStar_Options.ml_ish ()  in
                                if uu____13024
                                then
                                  let uu____13031 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____13034 =
                                    FStar_TypeChecker_Rel.conj_guard guard1 g
                                     in
                                  (uu____13031, uu____13034)
                                else
                                  (let uu____13038 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____13041 =
                                     FStar_TypeChecker_Rel.conj_guard guard1
                                       g
                                      in
                                   (uu____13038, uu____13041))
                             in
                          (match uu____12973 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____13060 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____13060
                                 then
                                   let uu____13061 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____13062 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____13063 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____13061 uu____13062 uu____13063
                                 else ());
                                (let g =
                                   let uu____13066 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____13066
                                    in
                                 let uu____13067 =
                                   FStar_TypeChecker_Rel.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____13067))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____13068;
                        FStar_Syntax_Syntax.pos = uu____13069;
                        FStar_Syntax_Syntax.vars = uu____13070;_},uu____13071)
                     ->
                     let uu____13106 =
                       FStar_List.fold_right
                         (fun uu____13135  ->
                            fun uu____13136  ->
                              match uu____13136 with
                              | (bs,guard1) ->
                                  let uu____13161 =
                                    let uu____13174 =
                                      let uu____13175 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____13175
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____13174
                                     in
                                  (match uu____13161 with
                                   | (t,uu____13191,g) ->
                                       let uu____13205 =
                                         let uu____13208 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____13208 :: bs  in
                                       let uu____13209 =
                                         FStar_TypeChecker_Rel.conj_guard g
                                           guard1
                                          in
                                       (uu____13205, uu____13209))) args
                         ([], guard)
                        in
                     (match uu____13106 with
                      | (bs,guard1) ->
                          let uu____13226 =
                            let uu____13233 =
                              let uu____13246 =
                                let uu____13247 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____13247
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____13246
                               in
                            match uu____13233 with
                            | (t,uu____13263,g) ->
                                let uu____13277 = FStar_Options.ml_ish ()  in
                                if uu____13277
                                then
                                  let uu____13284 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____13287 =
                                    FStar_TypeChecker_Rel.conj_guard guard1 g
                                     in
                                  (uu____13284, uu____13287)
                                else
                                  (let uu____13291 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____13294 =
                                     FStar_TypeChecker_Rel.conj_guard guard1
                                       g
                                      in
                                   (uu____13291, uu____13294))
                             in
                          (match uu____13226 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____13313 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____13313
                                 then
                                   let uu____13314 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____13315 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____13316 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____13314 uu____13315 uu____13316
                                 else ());
                                (let g =
                                   let uu____13319 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____13319
                                    in
                                 let uu____13320 =
                                   FStar_TypeChecker_Rel.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____13320))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____13339 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____13339 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____13361 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____13361)  in
                          tc_args head_info ([], [], [], guard, []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____13399) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____13405,uu____13406) ->
                     check_function_app t guard
                 | uu____13447 ->
                     let uu____13448 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____13448
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Rel.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
                  let uu____13520 =
                    FStar_List.fold_left2
                      (fun uu____13579  ->
                         fun uu____13580  ->
                           fun uu____13581  ->
                             match (uu____13579, uu____13580, uu____13581)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____13697 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____13697 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____13723 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____13723 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____13727 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____13727)
                                              &&
                                              (let uu____13729 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____13729))
                                          in
                                       let uu____13730 =
                                         let uu____13739 =
                                           let uu____13748 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____13748]  in
                                         FStar_List.append seen uu____13739
                                          in
                                       let uu____13773 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____13730, uu____13773, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____13520 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____13825 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____13825
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____13827 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____13827 with | (c2,g) -> (e, c2, g)))
              | uu____13843 ->
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
        let uu____13886 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____13886 with
        | (pattern,when_clause,branch_exp) ->
            let uu____13931 = branch1  in
            (match uu____13931 with
             | (cpat,uu____13972,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____14049 = FStar_Syntax_Util.type_u ()  in
                     match uu____14049 with
                     | (tu,u) ->
                         let uu____14060 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____14060 with
                          | (t1,uu____14072,g) -> (t1, g))
                      in
                   let uu____14074 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____14074 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____14108 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____14108
                         then
                           let uu____14109 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____14110 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____14109 uu____14110
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____14113 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____14113 with
                         | (env1,uu____14135) ->
                             let env11 =
                               let uu___117_14141 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___117_14141.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___117_14141.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___117_14141.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___117_14141.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___117_14141.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___117_14141.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___117_14141.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___117_14141.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___117_14141.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___117_14141.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___117_14141.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___117_14141.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___117_14141.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___117_14141.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___117_14141.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___117_14141.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___117_14141.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___117_14141.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___117_14141.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___117_14141.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___117_14141.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___117_14141.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___117_14141.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___117_14141.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___117_14141.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___117_14141.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___117_14141.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___117_14141.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___117_14141.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___117_14141.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___117_14141.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___117_14141.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___117_14141.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___117_14141.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___117_14141.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___117_14141.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___117_14141.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___117_14141.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____14144 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____14144
                               then
                                 let uu____14145 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____14146 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____14145 uu____14146
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____14149 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____14149 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___118_14174 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___118_14174.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___118_14174.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___118_14174.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____14175 =
                                     let uu____14176 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____14176
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14178 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____14178
                                         (FStar_TypeChecker_Rel.resolve_implicits
                                            env13)
                                     else
                                       (let uu____14180 =
                                          let uu____14185 =
                                            let uu____14186 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____14187 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____14186 uu____14187
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____14185)
                                           in
                                        FStar_Errors.raise_error uu____14180
                                          exp1.FStar_Syntax_Syntax.pos)
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs_to_string uvs =
                                     let uu____14199 =
                                       let uu____14202 =
                                         FStar_Util.set_elements uvs  in
                                       FStar_All.pipe_right uu____14202
                                         (FStar_List.map
                                            (fun u  ->
                                               FStar_Syntax_Print.uvar_to_string
                                                 u.FStar_Syntax_Syntax.ctx_uvar_head))
                                        in
                                     FStar_All.pipe_right uu____14199
                                       (FStar_String.concat ", ")
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____14220 =
                                       FStar_TypeChecker_Env.debug env
                                         (FStar_Options.Other "Free")
                                        in
                                     if uu____14220
                                     then
                                       ((let uu____14222 =
                                           FStar_Syntax_Print.term_to_string
                                             norm_exp
                                            in
                                         let uu____14223 = uvs_to_string uvs1
                                            in
                                         FStar_Util.print2
                                           ">> free_1(%s) = %s\n" uu____14222
                                           uu____14223);
                                        (let uu____14224 =
                                           FStar_Syntax_Print.term_to_string
                                             expected_pat_t
                                            in
                                         let uu____14225 = uvs_to_string uvs2
                                            in
                                         FStar_Util.print2
                                           ">> free_2(%s) = %s\n" uu____14224
                                           uu____14225))
                                     else ());
                                    (let uu____14228 =
                                       let uu____14229 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____14229
                                        in
                                     if uu____14228
                                     then
                                       let unresolved =
                                         FStar_Util.set_difference uvs1 uvs2
                                          in
                                       let uu____14233 =
                                         let uu____14238 =
                                           let uu____14239 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____14240 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____14241 =
                                             uvs_to_string unresolved  in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____14239 uu____14240
                                             uu____14241
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____14238)
                                          in
                                       FStar_Errors.raise_error uu____14233
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____14244 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____14244
                                     then
                                       let uu____14245 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____14245
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
                 let uu____14254 =
                   let uu____14261 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____14261
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____14254 with
                  | (scrutinee_env,uu____14294) ->
                      let uu____14299 = tc_pat true pat_t pattern  in
                      (match uu____14299 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____14349 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____14379 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____14379
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____14397 =
                                      let uu____14404 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____14404 e  in
                                    match uu____14397 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____14349 with
                            | (when_clause1,g_when) ->
                                let uu____14457 = tc_term pat_env branch_exp
                                   in
                                (match uu____14457 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Rel.conj_guard
                                         guard_pat_annots g_branch
                                        in
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____14511 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_17  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_17) uu____14511
                                        in
                                     let uu____14522 =
                                       let eqs =
                                         let uu____14543 =
                                           let uu____14544 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____14544  in
                                         if uu____14543
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____14557 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____14574 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____14577 ->
                                                FStar_Pervasives_Native.None
                                            | uu____14580 ->
                                                let uu____14581 =
                                                  let uu____14584 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____14584 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14581)
                                          in
                                       let uu____14587 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____14587 with
                                       | (c1,g_branch2) ->
                                           let uu____14612 =
                                             match (eqs, when_condition) with
                                             | uu____14629 when
                                                 let uu____14642 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____14642
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
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf
                                                    in
                                                 let uu____14672 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____14673 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____14672, uu____14673)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____14694 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____14694
                                                    in
                                                 let uu____14695 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____14696 =
                                                   let uu____14697 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____14697 g_when
                                                    in
                                                 (uu____14695, uu____14696)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w
                                                    in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w
                                                    in
                                                 let uu____14715 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____14715, g_when)
                                              in
                                           (match uu____14612 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____14751 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak)
                                                       in
                                                    if uu____14751
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak  in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1
                                                   in
                                                let uu____14753 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____14753, g_branch2))
                                        in
                                     (match uu____14522 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____14800 =
                                              let uu____14801 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____14801
                                               in
                                            if uu____14800
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____14843 =
                                                     let uu____14844 =
                                                       let uu____14845 =
                                                         let uu____14848 =
                                                           let uu____14855 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____14855
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____14848
                                                          in
                                                       FStar_List.length
                                                         uu____14845
                                                        in
                                                     uu____14844 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____14843
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____14861 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____14861 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____14882 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                (Prims.parse_int "1"))
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____14897 =
                                                             let uu____14902
                                                               =
                                                               let uu____14903
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____14903]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____14902
                                                              in
                                                           uu____14897
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____14924 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____14924]
                                                   else []  in
                                                 let fail1 uu____14931 =
                                                   let uu____14932 =
                                                     let uu____14933 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____14934 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____14935 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____14933
                                                       uu____14934
                                                       uu____14935
                                                      in
                                                   failwith uu____14932  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____14948) ->
                                                       head_constructor t1
                                                   | uu____14953 -> fail1 ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____14957 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____14957
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____14962 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____14977;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____14978;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____14979;_},uu____14980)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____15015 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____15017 =
                                                       let uu____15018 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____15018
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____15017]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____15019 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____15027 =
                                                       let uu____15028 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____15028
                                                        in
                                                     if uu____15027
                                                     then []
                                                     else
                                                       (let uu____15032 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____15032)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____15035 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____15037 =
                                                       let uu____15038 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____15038
                                                        in
                                                     if uu____15037
                                                     then []
                                                     else
                                                       (let uu____15042 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____15042)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____15068 =
                                                       let uu____15069 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____15069
                                                        in
                                                     if uu____15068
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____15076 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____15108
                                                                     ->
                                                                    match uu____15108
                                                                    with
                                                                    | 
                                                                    (ei,uu____15118)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____15124
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____15124
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____15145
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____15159
                                                                    =
                                                                    let uu____15164
                                                                    =
                                                                    let uu____15165
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____15165
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____15166
                                                                    =
                                                                    let uu____15167
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____15167]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____15164
                                                                    uu____15166
                                                                     in
                                                                    uu____15159
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15076
                                                            FStar_List.flatten
                                                           in
                                                        let uu____15194 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____15194
                                                          sub_term_guards)
                                                 | uu____15197 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____15213 =
                                                   let uu____15214 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____15214
                                                    in
                                                 if uu____15213
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____15217 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____15217
                                                       in
                                                    let uu____15226 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____15226 with
                                                    | (k,uu____15232) ->
                                                        let uu____15233 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____15233
                                                         with
                                                         | (t1,uu____15241,uu____15242)
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
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch2
                                             in
                                          ((let uu____15254 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____15254
                                            then
                                              let uu____15255 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____15255
                                            else ());
                                           (let uu____15257 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            let uu____15274 =
                                              let uu____15275 =
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.mk_binder
                                                  pat_bvs1
                                                 in
                                              FStar_TypeChecker_Util.close_guard_implicits
                                                env uu____15275 guard
                                               in
                                            (uu____15257, branch_guard,
                                              effect_label, cflags,
                                              maybe_return_c, uu____15274)))))))))

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
          let uu____15316 = check_let_bound_def true env1 lb  in
          (match uu____15316 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____15338 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15359 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____15359, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____15364 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____15364
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____15366 =
                      let uu____15379 =
                        let uu____15394 =
                          let uu____15403 =
                            let uu____15410 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____15410)
                             in
                          [uu____15403]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____15394
                         in
                      FStar_List.hd uu____15379  in
                    match uu____15366 with
                    | (uu____15445,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Rel.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Rel.abstract_guard_n gvs g12  in
                        let uu____15459 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____15459))
                  in
               (match uu____15338 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____15476 =
                      let uu____15485 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____15485
                      then
                        let uu____15494 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____15494 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____15523 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____15523
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____15524 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____15524, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____15538 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____15538
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm;
                                 FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____15544 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____15544
                            then e2
                            else
                              ((let uu____15549 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____15549
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
                    (match uu____15476 with
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
                         let uu____15576 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____15587 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____15576, uu____15587,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____15588 -> failwith "Impossible"

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
            let uu___119_15619 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___119_15619.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___119_15619.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___119_15619.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___119_15619.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___119_15619.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___119_15619.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___119_15619.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___119_15619.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___119_15619.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___119_15619.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___119_15619.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___119_15619.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___119_15619.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___119_15619.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___119_15619.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___119_15619.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___119_15619.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___119_15619.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___119_15619.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___119_15619.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___119_15619.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___119_15619.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___119_15619.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___119_15619.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___119_15619.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___119_15619.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___119_15619.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___119_15619.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___119_15619.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___119_15619.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___119_15619.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___119_15619.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___119_15619.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___119_15619.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___119_15619.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___119_15619.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___119_15619.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___119_15619.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____15620 =
            let uu____15631 =
              let uu____15632 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____15632 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____15631 lb  in
          (match uu____15620 with
           | (e1,uu____15654,c1,g1,annotated) ->
               ((let uu____15659 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____15663 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____15663)
                    in
                 if uu____15659
                 then
                   let uu____15664 =
                     let uu____15669 =
                       let uu____15670 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____15671 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____15670 uu____15671
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____15669)
                      in
                   FStar_Errors.raise_error uu____15664
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___120_15674 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___120_15674.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___120_15674.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____15675 =
                   let uu____15680 =
                     let uu____15681 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____15681]  in
                   FStar_Syntax_Subst.open_term uu____15680 e2  in
                 match uu____15675 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____15713 = tc_term env_x e21  in
                     (match uu____15713 with
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
                            let uu____15738 =
                              let uu____15745 =
                                let uu____15746 =
                                  let uu____15759 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____15759)  in
                                FStar_Syntax_Syntax.Tm_let uu____15746  in
                              FStar_Syntax_Syntax.mk uu____15745  in
                            uu____15738 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____15777 =
                              let uu____15778 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____15779 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____15778
                                c1.FStar_Syntax_Syntax.res_typ uu____15779
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_18  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_18)
                              uu____15777
                             in
                          let g21 =
                            let uu____15781 =
                              let uu____15782 =
                                FStar_TypeChecker_Rel.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Rel.imp_guard uu____15782 g2
                               in
                            FStar_TypeChecker_Rel.close_guard env2 xb
                              uu____15781
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Rel.conj_guard g1 g22
                             in
                          let uu____15785 =
                            let uu____15786 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____15786  in
                          if uu____15785
                          then
                            let tt =
                              let uu____15796 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____15796
                                FStar_Option.get
                               in
                            ((let uu____15802 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____15802
                              then
                                let uu____15803 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____15804 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____15803 uu____15804
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____15807 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____15807 with
                             | (t,g_ex) ->
                                 ((let uu____15821 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____15821
                                   then
                                     let uu____15822 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____15823 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____15822 uu____15823
                                   else ());
                                  (let uu____15825 =
                                     FStar_TypeChecker_Rel.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___121_15827 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___121_15827.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___121_15827.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___121_15827.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____15825))))))))
      | uu____15828 -> failwith "Impossible"

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
          let uu____15860 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____15860 with
           | (lbs1,e21) ->
               let uu____15879 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____15879 with
                | (env0,topt) ->
                    let uu____15898 = build_let_rec_env true env0 lbs1  in
                    (match uu____15898 with
                     | (lbs2,rec_env) ->
                         let uu____15917 = check_let_recs rec_env lbs2  in
                         (match uu____15917 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____15937 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____15937
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____15943 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____15943
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
                                     let uu____15992 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____16026 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____16026)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____15992
                                      in
                                   FStar_List.map2
                                     (fun uu____16060  ->
                                        fun lb  ->
                                          match uu____16060 with
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
                                let uu____16108 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____16108
                                 in
                              let uu____16109 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____16109 with
                               | (lbs5,e22) ->
                                   ((let uu____16129 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____16129
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____16130 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____16130, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____16141 -> failwith "Impossible"

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
          let uu____16173 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____16173 with
           | (lbs1,e21) ->
               let uu____16192 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____16192 with
                | (env0,topt) ->
                    let uu____16211 = build_let_rec_env false env0 lbs1  in
                    (match uu____16211 with
                     | (lbs2,rec_env) ->
                         let uu____16230 = check_let_recs rec_env lbs2  in
                         (match uu____16230 with
                          | (lbs3,g_lbs) ->
                              let uu____16249 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___122_16272 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___122_16272.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___122_16272.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___123_16274 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___123_16274.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____16249 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____16301 = tc_term env2 e21  in
                                   (match uu____16301 with
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
                                          let uu____16320 =
                                            let uu____16321 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____16321 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____16320
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
                                          let uu___124_16329 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___124_16329.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___124_16329.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___124_16329.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____16337 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____16337))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____16338 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____16338 with
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
                                                  uu____16376 ->
                                                  (e, cres4, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____16377 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____16377 with
                                                   | (tres1,g_ex) ->
                                                       let cres5 =
                                                         let uu___125_16391 =
                                                           cres4  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___125_16391.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___125_16391.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___125_16391.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____16392 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres5,
                                                         uu____16392))))))))))
      | uu____16393 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____16436 = FStar_Options.ml_ish ()  in
          if uu____16436
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____16439 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____16439 with
             | (formals,c) ->
                 let uu____16464 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____16464 with
                  | (actuals,uu____16474,uu____16475) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____16488 =
                          let uu____16493 =
                            let uu____16494 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____16495 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____16494 uu____16495
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____16493)
                           in
                        FStar_Errors.raise_error uu____16488
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____16498 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____16498 actuals
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
                                (let uu____16519 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____16519)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____16537 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____16537)
                               in
                            let msg =
                              let uu____16545 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____16546 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____16545 uu____16546 formals_msg
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
        let uu____16553 =
          FStar_List.fold_left
            (fun uu____16579  ->
               fun lb  ->
                 match uu____16579 with
                 | (lbs1,env1) ->
                     let uu____16599 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____16599 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let t1 =
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____16624 =
                                 let uu____16631 =
                                   let uu____16632 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____16632
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___126_16643 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___126_16643.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___126_16643.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___126_16643.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___126_16643.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___126_16643.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___126_16643.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___126_16643.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___126_16643.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___126_16643.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___126_16643.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___126_16643.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___126_16643.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___126_16643.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___126_16643.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___126_16643.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___126_16643.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___126_16643.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___126_16643.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___126_16643.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___126_16643.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___126_16643.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___126_16643.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___126_16643.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___126_16643.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___126_16643.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___126_16643.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___126_16643.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___126_16643.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___126_16643.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___126_16643.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___126_16643.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___126_16643.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___126_16643.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___126_16643.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___126_16643.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___126_16643.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___126_16643.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___126_16643.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____16631
                                  in
                               match uu____16624 with
                               | (t1,uu____16647,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       env2 g
                                      in
                                   ((let uu____16651 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left (fun a237  -> ())
                                       uu____16651);
                                    norm env01 t1))
                             in
                          let env3 =
                            let uu____16653 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____16653
                            then
                              let uu___127_16654 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___127_16654.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___127_16654.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___127_16654.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___127_16654.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___127_16654.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___127_16654.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___127_16654.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___127_16654.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___127_16654.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___127_16654.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___127_16654.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___127_16654.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___127_16654.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___127_16654.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___127_16654.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___127_16654.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___127_16654.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___127_16654.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___127_16654.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___127_16654.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___127_16654.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___127_16654.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___127_16654.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___127_16654.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___127_16654.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___127_16654.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___127_16654.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___127_16654.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___127_16654.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___127_16654.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___127_16654.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___127_16654.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___127_16654.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___127_16654.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___127_16654.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___127_16654.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___127_16654.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___127_16654.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___128_16667 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___128_16667.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___128_16667.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___128_16667.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___128_16667.FStar_Syntax_Syntax.lbpos)
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____16553 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____16690 =
        let uu____16699 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____16725 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____16725 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____16753 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____16753
                       | uu____16758 ->
                           let lb1 =
                             let uu___129_16761 = lb  in
                             let uu____16762 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16762;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___129_16761.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____16765 =
                             let uu____16772 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____16772
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____16765 with
                            | (e,c,g) ->
                                ((let uu____16781 =
                                    let uu____16782 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____16782  in
                                  if uu____16781
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
        FStar_All.pipe_right uu____16699 FStar_List.unzip  in
      match uu____16690 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard
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
        let uu____16831 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____16831 with
        | (env1,uu____16849) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____16857 = check_lbtyp top_level env lb  in
            (match uu____16857 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____16901 =
                     tc_maybe_toplevel_term
                       (let uu___130_16910 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___130_16910.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___130_16910.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___130_16910.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___130_16910.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___130_16910.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___130_16910.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___130_16910.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___130_16910.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___130_16910.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___130_16910.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___130_16910.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___130_16910.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___130_16910.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___130_16910.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___130_16910.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___130_16910.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___130_16910.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___130_16910.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___130_16910.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___130_16910.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___130_16910.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___130_16910.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___130_16910.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___130_16910.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___130_16910.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___130_16910.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___130_16910.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___130_16910.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___130_16910.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___130_16910.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___130_16910.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___130_16910.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___130_16910.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___130_16910.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___130_16910.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___130_16910.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___130_16910.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___130_16910.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____16901 with
                   | (e12,c1,g1) ->
                       let uu____16924 =
                         let uu____16929 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____16934  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____16929 e12 c1 wf_annot
                          in
                       (match uu____16924 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____16949 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____16949
                              then
                                let uu____16950 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____16951 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____16952 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____16950 uu____16951 uu____16952
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
            let uu____16986 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____16986 with
             | (univ_opening,univ_vars1) ->
                 let uu____17019 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, uu____17019))
        | uu____17024 ->
            let uu____17025 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____17025 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____17074 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____17074)
                 else
                   (let uu____17080 = FStar_Syntax_Util.type_u ()  in
                    match uu____17080 with
                    | (k,uu____17100) ->
                        let uu____17101 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____17101 with
                         | (t2,uu____17123,g) ->
                             ((let uu____17126 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____17126
                               then
                                 let uu____17127 =
                                   let uu____17128 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____17128
                                    in
                                 let uu____17129 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____17127 uu____17129
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____17132 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____17132))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____17138  ->
      match uu____17138 with
      | (x,imp) ->
          let uu____17157 = FStar_Syntax_Util.type_u ()  in
          (match uu____17157 with
           | (tu,u) ->
               ((let uu____17177 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____17177
                 then
                   let uu____17178 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____17179 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____17180 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____17178 uu____17179 uu____17180
                 else ());
                (let uu____17182 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____17182 with
                 | (t,uu____17202,g) ->
                     let x1 =
                       ((let uu___131_17210 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___131_17210.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___131_17210.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____17212 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____17212
                       then
                         let uu____17213 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____17214 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____17213 uu____17214
                       else ());
                      (let uu____17216 = push_binding env x1  in
                       (x1, uu____17216, g, u))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____17310 = tc_binder env1 b  in
            (match uu____17310 with
             | (b1,env',g,u) ->
                 let uu____17351 = aux env' bs2  in
                 (match uu____17351 with
                  | (bs3,env'1,g',us) ->
                      let uu____17404 =
                        let uu____17405 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____17405  in
                      ((b1 :: bs3), env'1, uu____17404, (u :: us))))
         in
      aux env bs

and (tc_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____17494  ->
             fun uu____17495  ->
               match (uu____17494, uu____17495) with
               | ((t,imp),(args1,g)) ->
                   let uu____17564 = tc_term env1 t  in
                   (match uu____17564 with
                    | (t1,uu____17582,g') ->
                        let uu____17584 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____17584))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____17626  ->
             match uu____17626 with
             | (pats1,g) ->
                 let uu____17651 = tc_args env p  in
                 (match uu____17651 with
                  | (args,g') ->
                      let uu____17664 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____17664))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____17677 = tc_maybe_toplevel_term env e  in
      match uu____17677 with
      | (e1,c,g) ->
          let uu____17693 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____17693
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____17704 =
               let uu____17709 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____17709
               then
                 let uu____17714 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____17714, false)
               else
                 (let uu____17716 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____17716, true))
                in
             match uu____17704 with
             | (target_comp,allow_ghost) ->
                 let uu____17725 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____17725 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____17735 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____17736 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, uu____17735, uu____17736)
                  | uu____17737 ->
                      if allow_ghost
                      then
                        let uu____17746 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____17746
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____17758 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____17758
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
      let uu____17781 = tc_tot_or_gtot_term env t  in
      match uu____17781 with
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
      (let uu____17813 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____17813
       then
         let uu____17814 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____17814
       else ());
      (let env1 =
         let uu___132_17817 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___132_17817.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___132_17817.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___132_17817.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___132_17817.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___132_17817.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___132_17817.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___132_17817.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___132_17817.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___132_17817.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___132_17817.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___132_17817.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___132_17817.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___132_17817.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___132_17817.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___132_17817.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___132_17817.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___132_17817.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___132_17817.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___132_17817.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___132_17817.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___132_17817.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___132_17817.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___132_17817.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___132_17817.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___132_17817.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___132_17817.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___132_17817.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___132_17817.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___132_17817.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___132_17817.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___132_17817.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___132_17817.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___132_17817.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___132_17817.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___132_17817.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___132_17817.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___132_17817.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____17824 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____17859) ->
             let uu____17860 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____17860
          in
       match uu____17824 with
       | (t,c,g) ->
           let uu____17876 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____17876
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____17884 =
                let uu____17889 =
                  let uu____17890 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____17890
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____17889)
                 in
              let uu____17891 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____17884 uu____17891))
  
let level_of_type_fail :
  'Auu____17906 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____17906
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____17922 =
          let uu____17927 =
            let uu____17928 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____17928 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____17927)  in
        let uu____17929 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____17922 uu____17929
  
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
          let uu____17964 =
            let uu____17965 = FStar_Syntax_Util.unrefine t1  in
            uu____17965.FStar_Syntax_Syntax.n  in
          match uu____17964 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____17969 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____17972 = FStar_Syntax_Util.type_u ()  in
                 match uu____17972 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___135_17980 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___135_17980.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___135_17980.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___135_17980.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___135_17980.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___135_17980.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___135_17980.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___135_17980.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___135_17980.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___135_17980.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___135_17980.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___135_17980.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___135_17980.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___135_17980.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___135_17980.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___135_17980.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___135_17980.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___135_17980.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___135_17980.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___135_17980.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___135_17980.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___135_17980.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___135_17980.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___135_17980.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___135_17980.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___135_17980.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___135_17980.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___135_17980.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___135_17980.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___135_17980.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___135_17980.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___135_17980.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___135_17980.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___135_17980.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___135_17980.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___135_17980.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___135_17980.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___135_17980.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___135_17980.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____17984 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____17984
                       | uu____17985 ->
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
      let uu____18002 =
        let uu____18003 = FStar_Syntax_Subst.compress e  in
        uu____18003.FStar_Syntax_Syntax.n  in
      match uu____18002 with
      | FStar_Syntax_Syntax.Tm_bvar uu____18008 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____18013 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____18040 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____18056) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____18102) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____18109 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____18109 with | ((uu____18120,t),uu____18122) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____18128 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____18128
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18131,(FStar_Util.Inl t,uu____18133),uu____18134) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18181,(FStar_Util.Inr c,uu____18183),uu____18184) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____18232 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____18241;
             FStar_Syntax_Syntax.vars = uu____18242;_},us)
          ->
          let uu____18248 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____18248 with
           | ((us',t),uu____18261) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____18267 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____18267)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____18283 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____18284 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18294) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18317 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____18317 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____18337  ->
                      match uu____18337 with
                      | (b,uu____18343) ->
                          let uu____18344 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____18344) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____18351 = universe_of_aux env res  in
                 level_of_type env res uu____18351  in
               let u_c =
                 let uu____18355 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____18355 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____18359 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____18359
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
            | FStar_Syntax_Syntax.Tm_bvar uu____18460 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____18475 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____18514 ->
                let uu____18515 = universe_of_aux env hd3  in
                (uu____18515, args1)
            | FStar_Syntax_Syntax.Tm_name uu____18528 ->
                let uu____18529 = universe_of_aux env hd3  in
                (uu____18529, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____18542 ->
                let uu____18557 = universe_of_aux env hd3  in
                (uu____18557, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____18570 ->
                let uu____18577 = universe_of_aux env hd3  in
                (uu____18577, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____18590 ->
                let uu____18617 = universe_of_aux env hd3  in
                (uu____18617, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____18630 ->
                let uu____18637 = universe_of_aux env hd3  in
                (uu____18637, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____18650 ->
                let uu____18651 = universe_of_aux env hd3  in
                (uu____18651, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____18664 ->
                let uu____18677 = universe_of_aux env hd3  in
                (uu____18677, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____18690 ->
                let uu____18697 = universe_of_aux env hd3  in
                (uu____18697, args1)
            | FStar_Syntax_Syntax.Tm_type uu____18710 ->
                let uu____18711 = universe_of_aux env hd3  in
                (uu____18711, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____18724,hd4::uu____18726) ->
                let uu____18791 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____18791 with
                 | (uu____18806,uu____18807,hd5) ->
                     let uu____18825 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____18825 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____18876 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env e
                   in
                let uu____18878 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____18878 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____18929 ->
                let uu____18930 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____18930 with
                 | (env1,uu____18952) ->
                     let env2 =
                       let uu___136_18958 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___136_18958.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___136_18958.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___136_18958.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___136_18958.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___136_18958.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___136_18958.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___136_18958.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___136_18958.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___136_18958.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___136_18958.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___136_18958.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___136_18958.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___136_18958.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___136_18958.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___136_18958.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___136_18958.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___136_18958.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___136_18958.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___136_18958.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___136_18958.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___136_18958.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___136_18958.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___136_18958.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___136_18958.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___136_18958.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___136_18958.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___136_18958.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___136_18958.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___136_18958.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___136_18958.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___136_18958.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___136_18958.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___136_18958.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___136_18958.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___136_18958.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___136_18958.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____18960 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____18960
                       then
                         let uu____18961 =
                           let uu____18962 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____18962  in
                         let uu____18963 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____18961 uu____18963
                       else ());
                      (let uu____18965 = tc_term env2 hd3  in
                       match uu____18965 with
                       | (uu____18986,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____18987;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____18989;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____18990;_},g)
                           ->
                           ((let uu____19004 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____19004
                               (fun a238  -> ()));
                            (t, args1)))))
             in
          let uu____19015 = type_of_head true hd1 args  in
          (match uu____19015 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____19055 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____19055 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____19099 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____19099)))
      | FStar_Syntax_Syntax.Tm_match (uu____19102,hd1::uu____19104) ->
          let uu____19169 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____19169 with
           | (uu____19172,uu____19173,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____19191,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____19238 = universe_of_aux env e  in
      level_of_type env e uu____19238
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____19263 = tc_binders env tps  in
      match uu____19263 with
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
      let uu____19317 =
        let uu____19318 = FStar_Syntax_Subst.compress t  in
        uu____19318.FStar_Syntax_Syntax.n  in
      match uu____19317 with
      | FStar_Syntax_Syntax.Tm_delayed uu____19323 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____19350 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____19355 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____19355
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____19357 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____19357
            (fun uu____19371  ->
               match uu____19371 with
               | (t1,uu____19379) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____19381;
             FStar_Syntax_Syntax.vars = uu____19382;_},us)
          ->
          let uu____19388 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____19388
            (fun uu____19402  ->
               match uu____19402 with
               | (t1,uu____19410) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____19412 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____19412
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____19414 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____19414
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____19419;_})
          ->
          let mk_comp =
            let uu____19459 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____19459
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____19487 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____19487
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____19554 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____19554
                 (fun u  ->
                    let uu____19562 =
                      let uu____19565 =
                        let uu____19572 =
                          let uu____19573 =
                            let uu____19586 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____19586)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____19573  in
                        FStar_Syntax_Syntax.mk uu____19572  in
                      uu____19565 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____19562))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____19620 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____19620 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____19673 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____19673
                       (fun uc  ->
                          let uu____19681 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____19681)
                 | (x,imp)::bs3 ->
                     let uu____19699 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____19699
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____19708 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____19726) ->
          let uu____19731 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____19731
            (fun u_x  ->
               let uu____19739 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____19739)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____19781 =
              let uu____19782 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____19782.FStar_Syntax_Syntax.n  in
            match uu____19781 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____19852 = FStar_Util.first_N n_args bs  in
                    match uu____19852 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____19926 =
                          let uu____19931 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____19931  in
                        (match uu____19926 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____19983 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____19983 with
                       | (bs1,c1) ->
                           let uu____20002 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____20002
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____20068  ->
                     match uu____20068 with
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
                         let uu____20126 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____20126)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____20128) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____20134,uu____20135) ->
                aux t1
            | uu____20176 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20177,(FStar_Util.Inl t1,uu____20179),uu____20180) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____20227,(FStar_Util.Inr c,uu____20229),uu____20230) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____20299 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____20299
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____20307) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____20312 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____20335 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____20348 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____20359 = type_of_well_typed_term env t  in
      match uu____20359 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____20365;
            FStar_Syntax_Syntax.vars = uu____20366;_}
          -> FStar_Pervasives_Native.Some u
      | uu____20369 -> FStar_Pervasives_Native.None

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
            let uu___137_20394 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___137_20394.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___137_20394.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___137_20394.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___137_20394.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___137_20394.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___137_20394.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___137_20394.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___137_20394.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___137_20394.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___137_20394.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___137_20394.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___137_20394.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___137_20394.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___137_20394.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___137_20394.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___137_20394.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___137_20394.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___137_20394.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___137_20394.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___137_20394.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___137_20394.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___137_20394.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___137_20394.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___137_20394.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___137_20394.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___137_20394.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___137_20394.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___137_20394.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___137_20394.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___137_20394.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___137_20394.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___137_20394.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___137_20394.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___137_20394.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___137_20394.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___137_20394.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___137_20394.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___137_20394.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____20400 =
            if must_total
            then
              let uu____20401 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____20401 with | (uu____20408,uu____20409,g) -> g
            else
              (let uu____20412 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____20412 with | (uu____20419,uu____20420,g) -> g)
             in
          let uu____20422 =
            let uu____20423 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____20423  in
          if uu____20422
          then slow_check ()
          else
            (let uu____20425 = type_of_well_typed_term env2 t  in
             match uu____20425 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____20430 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____20430
                   then
                     let uu____20431 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____20432 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____20433 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____20434 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____20431 uu____20432 uu____20433 uu____20434
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____20438 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____20438
                    then
                      let uu____20439 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____20440 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____20441 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____20442 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____20439 (if b then "succeeded" else "failed")
                        uu____20440 uu____20441 uu____20442
                    else ());
                   if b
                   then FStar_TypeChecker_Rel.trivial_guard
                   else slow_check ())))
  